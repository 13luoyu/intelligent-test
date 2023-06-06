import copy
import pprint
from transfer import mydsl_to_rules
import re
from ours.process_tco_to_r1 import is_num_key, is_price_key, is_time_key


def preprocess(rules):

    for rule_id in rules:
        rule = rules[rule_id]
        constraints = rule["constraints"]
        saved_op = ""
        to_add = []
        del_op = -1
        for pl, constraint in enumerate(constraints):
            key = constraint["key"]
            value = constraint["value"]
            # 时间
            if key == "op":
                saved_op = value
                del_op = pl
                continue
            if is_time_key(key):
                valid, new_value = time_preprocess(value)
                if valid:
                    constraint["value"] = new_value
                    constraint["operation"] = "in"
                else:
                    constraint["value"] = value
                    constraint["operation"] = "is"
            elif is_num_key(key):
                # 数量
                if saved_op != "":
                    value = saved_op + value
                    saved_op = ""
                valid, new_value = num_preprocess(value)
                if valid:
                    for i, v in enumerate(new_value):
                        if i == 0:
                            constraint["value"] = v
                            constraint["operation"] = "compute"
                        else:
                            new_constraint = {"key":key, "operation":"compute", "value":v}
                            to_add.append(new_constraint)
                else:
                    constraint["value"] = value
                    constraint["operation"] = "is"
            elif is_price_key(key):
                # 价格
                valid, new_value = price_preprocess(value)
                if valid:
                    constraint["value"] = new_value
                    constraint["operation"] = "compute"
                else:
                    constraint["value"] = value
                    constraint["operation"] = "is"
            else:
                constraint["operation"] = "is"
        constraints += to_add
        if del_op != -1:
            del constraints[del_op]
    return rules


def find_word(s, word):
        locs = [s.find(word)]
        while(locs[-1] != -1):
            locs.append(s.find(word, locs[-1] + 1))
        locs.pop()
        return locs


def time_preprocess(value):
    # 时间
    time_re = r"\d+:\d+"
    time_vals = re.findall(time_re, value)
    vals_locs = [value.find(time_val) for time_val in time_vals]
    loc_1s = find_word(value, "至")
    loc_2s = find_word(value, "前")
    loc_3s = find_word(value, "后")
    locs = sorted(loc_1s + loc_2s + loc_3s)
    if len(time_vals) > 0:
        t = "{"
        # 考虑三种时间的情况，9:00-10:00，9:00后，9:00前，其他情况直接照抄
        if len(vals_locs) != 2 * len(loc_1s) + len(loc_2s) + len(loc_3s):
            return False, ""
        p = 0
        valid = True
        for loc in locs:
            if loc in loc_1s:
                vl1, vl2 = vals_locs[p], vals_locs[p+1]
                if vl1 < loc and vl2 > loc:  # 合法
                    t += f"[{time_vals[p]}-{time_vals[p+1]}],"
                    p += 2
                else:  # 非法，直接不处理
                    valid = False
                    break
            elif loc in loc_2s:
                vl = vals_locs[p]
                if vl < loc:
                    t += f"[?-{time_vals[p]}],"
                    p += 1
                else:
                    valid = False
                    break
            else:  # loc in loc_3s
                vl = vals_locs[p]
                if vl < loc:
                    t += f"[{time_vals[p]}-?]"
                    p += 1
                else:
                    valid = False
                    break
        if valid:
            t = t[:-1] + "}"
            return True, t
        else:
            return False, ""
    return False, "Not Time"

def judge_op(value):
    value = value.replace("得", "")
    
    if "不低于" in value or "达到" in value or "以上" in value:
        return ">="
    if "不高于" in value or "以下" in value or "不超过" in value:
        return "<="
    if "低于" in value or "未达到" in value or "不足" in value:
        return "<"
    if "高于" in value or "超过" in value or "优于" in value:
        return ">"
    if "等于" in value:
        return "=="
    if "不等于" in value:
        return "!="
    return ""


def num_preprocess(value):
    vs = value.split(",")
    num_re = "\d+"
    t = []
    for v in vs:  # 一个v中只能有一个数字，不然报错
        num_vals = re.findall(num_re, v)
        if len(num_vals) != 1:
            return False, f"句子\"{v}\"中数字不是一个"
        num_val = num_vals[0]
        val_loc = v.find(num_val)
        unit_loc = val_loc + len(num_val)
        while(v[unit_loc] == "亿" or v[unit_loc] == "万"):
            if v[unit_loc] == "万":
                num_val += "0000"
            elif v[unit_loc] == "亿":
                num_val += "00000000"
            unit_loc += 1
        op = judge_op(v)
        if op != "":
            t.append([op, num_val])
        if "整数倍" in v:
            t.append(["%", num_val, "==", "0"])
    if len(t) == 0:
        return False, f"句子\"{v}\"中没有约束"
    return True, t



def price_preprocess(value):
    price_re = r"\d+(.\d+)?"
    price_vals = re.findall(price_re, value)
    if len(price_vals) == 1:
        return True, ["==", price_vals[0]]
    else:
        return False, ""



def compose_rules_r1_r2(defines, vars, rules, preliminaries, rule_name = "rule"):
    """
    规则组合函数, 包含:
    1. 组合明显嵌套的规则
    2. 补全单规则相关的字段
    3. 必须交易阶段相同，一个是订单连续性操作，一个是交易时间，组合
       此外，这一步还会去重
    4. 补全"其他"交易方式等
    5. 申报数量<100...0和其他规则的组合, 同一rule下subrule的组合
    6. 除本规则规定的不接受撤销申报的时间段外，其他接受申报的时间内怎样怎样
    7. 没有then就删掉，这是另一个去重步
    """
    # 预处理：添加两个结合规则
    vars, rules = add_relation(vars, rules)
    # 组合明显嵌套的规则
    vars, rules = compose_nested_rules(vars, rules)
    # 必须交易阶段相同，一个是订单连续性操作，一个是交易时间，组合
    vars, rules = compose_same_stage(vars, rules)
    # "其他"补全
    vars, rules = supply_other_rules(vars, rules, preliminaries)

    # 补全单规则相关的字段
    vars, rules = supply_rules_on_prelim(defines, vars, rules, preliminaries)

    # 申报数量<100...0和其他规则的组合, 同一rule下subrule的组合  ID有问题 FIXME
    vars, rules = subrule_compose(vars, rules)

    # 除本规则规定的不接受撤销申报的时间段外，其他接受申报的时间内怎样怎样
    vars, rules = compute_other_time_in_rules(vars, rules, preliminaries)
    
    # 没有then就删掉
    vars, rules = delete_then(vars, rules)


    # 打印中间结果
    # with open(f"rules/r2_{rule_name}.txt", "w", encoding="utf-8") as f:
    #     f.write(pprint.pformat(rules))
    # print(f"R2包含的规则数：{len(vars.keys())}")
    
    return defines, vars, rules











def add_relation(vars, rules):

    # 遍历，找到没有then的所有规则，以及所有结合规则
    keys = list(rules.keys())
    rule_class_all, rule_class_have = [], []
    last = ""
    for rule_id in keys:
        rule = rules[rule_id]
        if "results" not in rule:
            if rule["rule_class"][0] not in rule_class_all:
                rule_class_all.append(rule["rule_class"][0])
        else:
            for c in rule["constraints"]:
                if c["key"] == "结合规则":
                    if c["value"][2:-2] not in rule_class_have:
                        rule_class_have.append(c["value"][2:-2])
                        last = rule_id
                    break
    # 所有要补充的规则
    rule_class_not_have = []
    for rule_id in rule_class_all:
        if rule_id not in rule_class_have:
            rule_class_not_have.append(rule_id)
    if last == "":
        last = "100.1.1.1"

    # 生成规则
    last_list = last.split(".")
    last_list[-1] = str(30)
    for i, id in enumerate(rule_class_not_have):
        new_id = ".".join(last_list)
        last_list[-1] = str(int(last_list[-1]) + 1)
        constraints = [{"key":"交易操作","operation":"is","value":"债券交易申报"},
                       {"key":"结合规则","operation":"in","value":f"['{id}']"},
                       {"key":"交易市场","operation":"is","value":"深圳证券交易所"},
                       {"key":"交易品种","operation":"is","value":"债券"}]
        results = [{"key":"结果","value":"成功","else":"失败"}]
        focus = ["订单连续性操作"]
        rule_class = [".".join(last_list[:-1])]
        rules[new_id] = {"constraints":constraints,"results":results,"focus":focus,"rule_class":rule_class}
        vars[new_id] = {"交易操作":[],"结合规则":[],"交易市场":[],"交易品种":[]}

        # print(new_id, rules[new_id], vars[new_id])
    return vars, rules





def compose_nested_rules(vars, rules):
    keys = list(rules.keys())
    # 组合明显嵌套的规则
    # if 结合规则 in ["3.1.5"]
    to_delete = []
    for rule_id in keys:
        rule = rules[rule_id]
        for c in rule['constraints']:
            if c['key'] == "结合规则":
                to_delete.append(rule_id)
                target_id = c['value'][2:-2]
                for trule_id in keys:
                    trule = rules[trule_id]
                    if target_id in trule_id:
                        # 组合
                        new_rule = copy.deepcopy(trule)
                        # constraints
                        for nc in rule['constraints']:
                            if nc['key'] == "结合规则":
                                continue
                            find = False
                            for oc in new_rule['constraints']:
                                if nc['key'] == oc['key']:
                                    find = True
                                    break
                            if not find:
                                new_rule['constraints'].append(nc)
                        if rule_id < trule_id:
                            new_id = rule_id + "," + trule_id
                        else:
                            new_id = trule_id + "," + rule_id
                        # results
                        if "results" not in new_rule:
                            if "results" in rule:
                                new_rule['results'] = copy.deepcopy(rule['results'])
                        else:
                            if "results" in rule:
                                for result in rule['results']:
                                    find = False
                                    for alread_have_result in new_rule['results']:
                                        if alread_have_result['key'] == result['key']:
                                            find = True
                                            break
                                    if not find:
                                        new_rule['results'].append(copy.deepcopy(result))
                        # focus
                        if "focus" not in new_rule:
                            if "focus" in rule:
                                new_rule["focus"] = copy.deepcopy(rule['focus'])
                        else:
                            if "focus" in rule:
                                for focus in rule["focus"]:
                                    if focus not in new_rule["focus"]:
                                        new_rule["focus"].append(focus)
                        # rule_class
                        for rule_idd in rule['rule_class']:
                            if rule_idd not in new_rule['rule_class']:
                                new_rule['rule_class'].append(rule_idd)
                        
                        
                        rules[new_id] = new_rule
                        
                        new_var = copy.deepcopy(vars[trule_id])
                        for var in vars[rule_id]:
                            if var not in new_var:
                                new_var[var] = []
                        del new_var['结合规则']
                        vars[new_id] = new_var

                break
    for id in to_delete:
        del rules[id]
        del vars[id]
    return vars, rules



def supply_rules_on_prelim(defines, vars, rules, preliminaries):
    # 如果规则中没有"单独可测试规则要素"，添加

    # preliminaries = json.load(open("preliminaries.json", "r", encoding="utf-8"))
    elements = preliminaries["单独可测试规则要素"]


    for element in elements:
        if element == "交易方向":
            # 交易操作
            for rule_id in list(rules.keys()):
                rule = rules[rule_id]
                for c in rule['constraints']:
                    if c['key'] == '交易操作':
                        if '买入' in c['value']:
                            rule['constraints'].append({"key":"交易方向","operation":"is","value":"买入"})
                            vars[rule_id]['交易方向'] = []
                        if '卖出' in c['value']:
                            rule['constraints'].append({"key":"交易方向","operation":"is","value":"卖出"})
                            vars[rule_id]['交易方向'] = []
        if element in defines:
            e = defines[element][0]
        else:
            e = preliminaries[element]

        if type(e) == str:
            for rule_id in list(rules.keys()):
                rule = rules[rule_id]
                find = False
                for c in rule["constraints"]:
                    if element == c["key"]:
                        find = True
                        break
                if not find:
                    constraint = {"key": element, "operation": "is", "value": e}
                    rule["constraints"].append(constraint)
                    vars[rule_id][element] = []
        elif type(e) == list:
            to_delete = []
            keys = list(rules.keys())
            for rule_id in keys:
                rule = rules[rule_id]
                find = False
                for c in rule["constraints"]:
                    if element == c["key"]:
                        find = True
                        break
                if not find:
                    for (i, ee) in enumerate(e):
                        new_rule = copy.deepcopy(rule)
                        new_rule["constraints"].append({"key": element, "operation":"is", "value":ee})
                        new_id = f"{rule_id}.{i+1}"
                        rules[new_id] = new_rule
                        new_var = copy.deepcopy(vars[rule_id])
                        new_var[element] = []
                        vars[new_id] = new_var
                    to_delete.append(rule_id)
            for id in to_delete:
                del rules[id]
                del vars[id]
    return vars, rules



def compose_same_stage(vars, rules):
    keys1 = list(vars.keys())

    stages = []  # 每个规则是否有交易阶段
    times = []  # 每个规则是否有交易时间
    for i in range(len(keys1)):
        rule_id = keys1[i]
        rule = rules[rule_id]
        have_stage = False
        have_time = False
        for c in rule["constraints"]:
            if c["key"] == "交易阶段":
                stages.append(c["value"])
                have_stage = True
            if c["key"] == "交易时间":
                times.append(c["value"])
                have_time = True
        if not have_stage:
            stages.append(None)
        if not have_time:
            times.append(None)

    to_delete = []
    for i in range(len(keys1)):
        if ',' in keys1[i]:
            continue
        for j in range(len(keys1)):
            if j <= i:
                continue
            if stages[i] is not None and stages[i] == stages[j]:# 都有交易阶段，且相同，且
                focusi = rules[keys1[i]]['focus']
                focusj = rules[keys1[j]]['focus']
                if "申报价格" in focusi or "申报价格" in focusj or "申报数量" in focusi or "申报数量" in focusj:
                    continue
                time_in_i, time_in_j, op_in_i, op_in_j = "交易时间" in focusi, "交易时间" in focusj, "订单连续性操作" in focusi, "订单连续性操作" in focusj
                if (time_in_i and op_in_j) or (time_in_j and op_in_i):# 一个是订单连续性操作，一个是交易时间
                    if times[i] is not None and times[j] is not None:  # 交易时间都不为空
                        if times[i] != times[j]:  # 交易时间不同，排除
                            continue
                    # 如果无冲突，组合
                    to_add = []
                    new_rule = copy.deepcopy(rules[keys1[i]])
                    conflict = False
                    for c in rules[keys1[j]]["constraints"]:
                        find = False
                        for c1 in new_rule["constraints"]:
                            if c["key"] == c1["key"] and (c["operation"] == "is" or c['operation'] == 'in'):
                                find = True
                                if c["value"] != c1["value"]:
                                    conflict = True
                                    break
                        if not find:
                            to_add.append(c)
                        if conflict:
                            break
                    if conflict:
                        continue
                    
                    for c in to_add:
                        new_rule["constraints"].append(c)
                    
                    # results
                    rule = rules[keys1[j]]
                    if "results" not in new_rule:
                        if "results" in rule:
                            new_rule['results'] = copy.deepcopy(rule['results'])
                    else:
                        if "results" in rule:
                            for result in rule['results']:
                                find = False
                                for alread_have_result in new_rule['results']:
                                    if alread_have_result['key'] == result['key']:
                                        find = True
                                        break
                                if not find:
                                    new_rule['results'].append(copy.deepcopy(result))
                    # focus
                    if "focus" not in new_rule:
                        if "focus" in rule:
                            new_rule["focus"] = copy.deepcopy(rule['focus'])
                    else:
                        if "focus" in rule:
                            for focus in rule["focus"]:
                                if focus not in new_rule["focus"]:
                                    new_rule["focus"].append(focus)
                    # rule_class
                    for rule_idd in rule['rule_class']:
                        if rule_idd not in new_rule['rule_class']:
                            new_rule['rule_class'].append(rule_idd)


                    # 这些长操作是为了去重id，比如3.1.5.1,3.1.5.1.1这样的
                    id1_list, id2_list = keys1[i].split(","), keys1[j].split(",")
                    id1_list, id2_list = sorted(id1_list), sorted(id2_list)
                    x, y = 0, 0
                    new_id = ""
                    while x < len(id1_list) and y < len(id2_list):
                        if id1_list[x] in id2_list[y]:
                            new_id += id1_list[x] + ","
                            x += 1
                            y += 1
                        elif id2_list[y] in id1_list[x]:
                            new_id += id2_list[y] + ","
                            x += 1
                            y += 1
                        elif id1_list[x] < id2_list[y]:
                            new_id += id1_list[x] + ","
                            x += 1
                        else:
                            new_id += id2_list[y] + ","
                            y += 1
                    while x < len(id1_list):
                        new_id += id1_list[x] + ","
                        x += 1
                    while y < len(id2_list):
                        new_id += id2_list[y] + ","
                        y += 1
                    new_id = new_id[:-1]

                    rules[new_id] = new_rule
                    if keys1[i] not in to_delete and keys1[i] != new_id:
                        to_delete.append(keys1[i])
                    if keys1[j] not in to_delete and keys1[j] != new_id:
                        to_delete.append(keys1[j])

                    new_var = copy.deepcopy(vars[keys1[i]])
                    for v in list(vars[keys1[j]].keys()):
                        if v not in list(new_var.keys()):
                            new_var[v] = []
                    vars[new_id] = new_var
    for id in to_delete:
        del rules[id]
        del vars[id]
    return vars, rules
                    




def supply_other_rules(vars, rules, preliminaries):
    to_delete = []
    keys = list(vars.keys())
    for rule_id in keys:
        rule = rules[rule_id]
        for c in rule["constraints"]:
            if c["value"] == "其他" + c["key"]:
                have = []
                rule_class = rule["rule_class"]
                for rule_id1 in keys:
                    if rule_class == rules[rule_id1]["rule_class"] and rule_id != rule_id1:
                        for c0 in rules[rule_id1]["constraints"]:
                            if c0['key'] == c["key"] and c0['value'] != c["value"] and c0["value"] not in have:
                                have.append(c0["value"])
                                break
                # 取反
                # preliminaries = json.load(open("preliminaries.json", "r", encoding="utf-8"))
                c_key = preliminaries[c["key"]]
                not_have = []
                for k in c_key:
                    if k not in have:
                        not_have.append(k)
                for i, k in enumerate(not_have):
                    new_rule = copy.deepcopy(rule)
                    new_var = copy.deepcopy(vars[rule_id])
                    new_id = f"{rule_id}.{i+1}"
                    for c1 in new_rule["constraints"]:
                        if c1["key"] == c["key"]:
                            c1["value"] = k
                            break
                    rules[new_id] = new_rule
                    vars[new_id] = new_var
                to_delete.append(rule_id)
    
    for id in to_delete:
        del vars[id]
        del rules[id]


    return vars, rules



def subrule_compose(vars, rules):
    # 同一rule下的subrule组合
    # 多组合

    to_delete = []
    while(1):
        keys = list(rules.keys())
        for i in range(len(keys)):
            for j in range(len(keys)):
                # 避免重复，并且要求属于同一个rule
                if j <= i or rules[keys[i]]["rule_class"] != rules[keys[j]]["rule_class"]:
                    continue
                # 避免冲突
                new_rule = copy.deepcopy(rules[keys[i]])
                conflict = False
                for c in rules[keys[j]]["constraints"]:
                    if c['operation'] == "in":
                        conflict = True
                        break
                    find = False
                    for c1 in new_rule["constraints"]:
                        if c1['operation'] == "in":
                            conflict = True
                            break
                        if c['key'] == c1['key'] and c['operation'] == "is":
                            find = True
                            if c['value'] != c1['value']:
                                conflict = True
                            break
                        if c['key'] == c1['key'] and c['operation'] == 'compute':
                            if c['value'] == c1['value']:
                                find = True
                        # # 特殊处理: 申报数量 == 100000   申报数量 % 100000 == 0
                        # if c['key'] == c1['key'] and c['operation'] == "compute":
                        #     if c['value'][1] == c1['value'][1]:
                        #         conflict = True
                        #         break
                    if conflict:
                        break
                    if not find:
                        new_rule["constraints"].append(copy.deepcopy(c))
                if conflict:
                    continue
                # 合并results, focus
                if "results" not in new_rule and "results" in rules[keys[j]]:
                    new_rule["results"] = copy.deepcopy(rules[keys[j]]["results"])
                elif "results" in new_rule and "results" in rules[keys[j]]:
                    for r in rules[keys[j]]['results']:
                        find = False
                        for r1 in new_rule['results']:
                            if r['key'] == r1['key']:
                                find = True
                                break
                        if not find:
                            new_rule['results'].append(copy.deepcopy(r))
                for f in rules[keys[j]]['focus']:
                    if f not in new_rule['focus']:
                        new_rule['focus'].append(f)
                if keys[i] not in to_delete:
                    to_delete.append(keys[i])
                if keys[j] not in to_delete:
                    to_delete.append(keys[j])
                keyi_list = keys[i].split(",")
                keyj_list = keys[j].split(",")
                for kj in keyj_list:
                    if kj not in keyi_list:
                        keyi_list.append(kj)
                keyi_list = sorted(keyi_list)

                del_index = []
                for pi, xi in enumerate(keyi_list):  # 3.1.5.1, 3.1.5
                    point_num=0
                    start = 0
                    pl = xi.find(".", start)
                    while(pl!=-1 and point_num <= 2):
                        point_num += 1
                        start = pl+1
                        pl = xi.find(".", start)
                    if pl == -1:
                        rule_class1 = xi
                    else:
                        rule_class1 = xi[:pl]
                    
                    for pj, xj in enumerate(keyi_list):
                        if pj <= pi:
                            continue
                        point_num=0
                        start = 0
                        pl = xj.find(".", start)
                        while(pl!=-1 and point_num <= 2):
                            point_num += 1
                            start = pl+1
                            pl = xj.find(".", start)
                        if pl == -1:
                            rule_class2 = xj
                        else:
                            rule_class2 = xj[:pl]
                        if rule_class1 == rule_class2:
                            if len(xi) > len(xj):
                                del_index.append(pi)
                            else:
                                del_index.append(pj)
                key_list = []
                for pi, xi in enumerate(keyi_list):
                    if pi not in del_index:
                        key_list.append(xi)

                    
                new_id = ",".join(key_list)
                rules[new_id] = new_rule


                # 更新vars
                new_var = copy.deepcopy(vars[keys[i]])
                for v in list(vars[keys[j]].keys()):
                    if v not in list(new_var.keys()):
                        new_var[v] = []
                vars[new_id] = new_var

        if len(to_delete) == 0:
            break
        for id in to_delete:
            del vars[id]
            del rules[id]
        to_delete = []
    return vars, rules




def compute_other_time_in_rules(vars, rules, preliminaries):
    # 处理“交易阶段 is "除本规则规定的不接受撤销申报的时间段外，其他接受申报的时间内"”这句话
    # 输入
# '3.3.12.1.1.1': {'constraints': [{'key': '交易阶段',
#                                    'operation': 'is',
#                                    'value': '除本规则规定的不接受撤销申报的时间段外，其他接受申报的时间内'},
#                                   {'key': '操作',
#                                    'operation': 'is',
#                                    'value': '撤销'},
#                                   {'key': '操作部分',
#                                    'operation': 'is',
#                                    'value': '未成交的申报'},
#                                   {'key': '交易市场',
#                                    'operation': 'is',
#                                    'value': '深圳证券交易所'},
#                                   {'key': '交易方式',
#                                    'operation': 'is',
#                                    'value': '匹配成交'},
#                                   {'key': '交易品种',
#                                    'operation': 'is',
#                                    'value': '债券'},
#                                   {'key': '交易方向',
#                                    'operation': 'is',
#                                    'value': '买入'}],
#                   'focus': ['订单连续性操作'],
#                   'results': [{'else': '不成功', 'key': '结果', 'value': '成功'}],
#                   'rule_class': ['3.3.12']}
    # 输出
    # 规则添加交易时间 in {[9:15-9:20],[9:30-11:30]}，删除交易阶段

    keys = list(rules.keys())
    for i in range(len(keys)):
        rule = rules[keys[i]]
        new_constraints = copy.deepcopy(rule['constraints'])
        for cnt, c in enumerate(rule['constraints']):
            if c['key'] == '交易阶段' and "除" in c['value'] and "外" in c['value'] and "其他" in c['value']:
                # 处理，添加交易时间
                sentence = c['value'].split('外')
                # preliminaries = json.load(open("preliminaries.json", "r", encoding="utf-8"))
                elements = preliminaries["单独可测试规则要素"]
                # 首先处理除...外，这中间有两个点用于匹配，一是操作“撤销”，二是结果“失败”
                # 遍历所有其他规则，寻找这两个点
                except_time = ""  # 除了这个时间段，要找的结果就是这个时间
                for j in range(len(keys)):
                    if j == i:
                        continue
                    other_rule = rules[keys[j]]
                    # 首先判断是否冲突，冲突的话下一个
                    conflict = False
                    for ic in rule['constraints']:
                        for jc in other_rule['constraints']:
                            if ic['key'] == jc['key'] and ic['key'] in elements:
                                if ic['value'] != jc['value']:
                                    conflict = True
                                break
                        if conflict:
                            break
                    if conflict:
                        continue
                    # 接下来寻找是否满足sentence[0]
                    find = False
                    for jc in other_rule['constraints']:
                        if jc['key'] == "交易操作" and '撤销' in jc['value'] and 'results' in other_rule:
                            # if "撤销" + jc['value'] in sentence[0]:  # 要的是撤销申报，而jc['value']是申报
                            #     break
                            for jr in other_rule['results']:
                                if jr['value'] == "失败":
                                    find = True
                                    break
                            if find:
                                break
                    if find:
                        for jc in other_rule['constraints']:
                            if jc['key'] == '交易时间':
                                except_time = jc['value'][1:-1]
                                break
                        break
                # 只有匹配成交才有except_time，其他都是空
                # 其他接受申报的时间内，有两个关键点，一个是操作“申报”，一个是结果“接受”
                expect_time = ""  # 本轮搜索期望找到的时间
                for j in range(len(keys)):
                    if j == i:
                        continue
                    other_rule = rules[keys[j]]
                    # 首先判断是否冲突，冲突的话下一个
                    conflict = False
                    for ic in rule['constraints']:
                        for jc in other_rule['constraints']:
                            if ic['key'] == jc['key'] and ic['key'] in elements:
                                if ic['value'] != jc['value']:
                                    conflict = True
                                break
                            if rule['rule_class'] == other_rule['rule_class']:
                                conflict = True
                                break
                        if conflict:
                            break
                    if conflict:
                        continue
                    # 接下来寻找是否满足sentence[1]
                    find = False
                    for jc in other_rule['constraints']:
                        # 债券交易申报
                        if jc['key'] == "交易操作" and '申报' in jc['value'] and 'results' in other_rule:
                            for jr in other_rule['results']:
                                if jr['value'] == '成功':
                                    find = True
                                    break
                            if find:
                                break
                    if find:  # 注意，这里和上面的except_time的find不同，这里可能有多条时间
                        for jc in other_rule['constraints']:
                            if jc['key'] == '交易时间':
                                expect_time += jc['value'][1:-1] + ","
                                break
                # 现在有了期望的时间expect_time，有了排除的时间except_time，计算差
                expect_time = expect_time[:-1]
                real_time = expect_time
                if except_time != "":
                    except_begin, except_end = except_time[1:-1].split("-")
                    if len(except_begin) == 4:
                        except_begin = '0' + except_begin
                    if len(except_end) == 4:
                        except_end = '0' + except_end
                    expect_list = expect_time.split(",")
                    l = []  # 将时间段拆成一个个时间点
                    for el in expect_list:
                        l += el[1:-1].split("-")
                    # l = ['9:15', '9:25', '9:30', '11:30', '13:00', '15:30']
                    for count in range(len(l)):
                        if len(l[count]) == 4:
                            l[count] = '0' + l[count]
                    if except_end <= l[0] or except_begin >= l[-1]:
                        break  # 无影响
                    real_time_list = []
                    for count in range(0, len(l), 2):
                        if except_end <= l[count] or except_begin >= l[count+1]:
                            real_time_list.append(l[count])
                            real_time_list.append(l[count+1])
                            continue
                        # 四种情况有交集，设a为realtime，b为excepttime，
                        # 有a1<=a2, b1<=b2
                        if l[count] <= except_begin and l[count+1] <= except_end:
                            real_time_list.append(l[count])
                            real_time_list.append(except_begin)
                        # a1<=a2, b1>=b2
                        elif l[count] <= except_begin and l[count+1] >= except_end:
                            real_time_list.append(l[count])
                            real_time_list.append(except_begin)
                            real_time_list.append(except_end)
                            real_time_list.append(l[count+1])
                        # a1>=a2, b1>=b2,
                        elif l[count] >= except_begin and l[count+1] >= except_end:
                            real_time_list.append(except_end)
                            real_time_list.append(l[count+1])
                        # a1>=a2, b1<=b2
                        else:
                            ...  # do nothing
                    s = "{"
                    for count in range(0, len(real_time_list), 2):
                        s += f"[{real_time_list[count]}-{real_time_list[count+1]}],"
                    real_time = s[:-1] + '}'
                if '{' not in real_time:
                    real_time = '{' + real_time + '}'
                constraint = {"key":"交易时间", "operation":"in", "value": real_time}
                new_constraints.append(constraint)
                # 处理完成
                # 删除交易阶段
                del new_constraints[cnt]
                rules[keys[i]]["constraints"] = new_constraints

                del vars[keys[i]]["交易阶段"]
                vars[keys[i]]['交易时间'] = []
                break

    return vars, rules



def delete_then(vars, rules):
    keys = list(rules.keys())
    to_delete = []
    for rule_id in keys:
        rule = rules[rule_id]
        if 'results' not in rule:
            to_delete.append(rule_id)
    for rule_id in to_delete:
        del rules[rule_id]
        del vars[rule_id]
    return vars, rules






































@DeprecationWarning
def compose_full_rules(vars, rules):
    # 全规则组合，太多了
    keys1 = list(vars.keys())

    composed_rules = {}
    for i in range(1 << len(keys1)):
        if i == 0:
            continue

        new_constraints = []
        new_results = []
        new_focus = []
        new_id = ""
        for j in range(len(keys1)):
            rule_now = rules[keys1[j]]
            if i & (1 << j):
                # 有这条规则，组合
                if new_constraints == []:
                    new_constraints = copy.deepcopy(rule_now['constraints'])
                    if "results" in rule_now:
                        new_results = copy.deepcopy(rule_now['results'])
                    new_focus = copy.deepcopy(rule_now['focus'])
                    new_id = keys1[j]
                    continue
                conflict = False
                to_add = []
                for c0 in rule_now['constraints']:
                    find = False
                    for c1 in new_constraints:
                        if c0['operation'] == 'is' and c0['key'] == c1['key']:
                            find = True
                            if c0['value'] != c1['value']:
                                conflict = True
                                break
                    if not find:
                        to_add.append(copy.deepcopy(c0))
                    if conflict:
                        break
                if not conflict:
                    new_constraints = new_constraints + to_add
                    new_id = new_id + "," + keys1[j]
                    if "results" in rule_now:
                        for r0 in rule_now['results']:
                            if r0 not in new_results:
                                new_results.append(r0)
                    for f0 in rule_now['focus']:
                        if f0 not in new_focus:
                            new_focus.append(f0)

        if new_results == []:
            t = {"constraints":new_constraints,
             "focus":new_focus}
        else:
            t = {"constraints":new_constraints,
                "results":new_results,
                "focus":new_focus}
        composed_rules[new_id] = t


    # 删除原来的组合规则，加入新的组合规则
    for key in keys1:
        del rules[key]
        del vars[key]
    for rule_id in composed_rules:
        rules[rule_id] = composed_rules[rule_id]
        var = {}
        for c in rules[rule_id]['constraints']:
            var[c['key']] = []
        vars[rule_id] = var

    # 去重
    # 去重组合规则，方法是如果一个a是另一个b的子集，去掉a
    keys = rules.keys()
    key_to_delete = []
    for i, rule_id in enumerate(keys):
        rule = rules[rule_id]
        if rule['focus'] == '交易时间':
            continue
        rule_id_list = rule_id.split(',')
        for j, rule_id1 in enumerate(keys):
            rule1 = rules[rule_id1]
            if rule1['focus'] == '交易时间' or i == j:
                continue
            rule_id_list1 = rule_id1.split(',')
            # 看是否rule_id_list1是rule_id_list的子集
            is_subset = True
            for x in rule_id_list1:
                if x not in rule_id_list:
                    is_subset = False
                    break
            if is_subset and rule_id1 not in key_to_delete:
                key_to_delete.append(rule_id1)

    for key in key_to_delete:
        del rules[key]
        del vars[key]



# if __name__ == "__main__":
#     defines, vars, rules = mydsl_to_rules.read_file("r1.mydsl")
#     rules = preprocess(rules)
#     pprint.pprint(rules)
#     exit(0)
#     compose_rules_r1_r2(defines, vars, rules)




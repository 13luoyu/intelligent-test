import copy
import pprint
import re
from ours.process_tco_to_r1 import is_num_key, is_price_key, is_time_key


def preprocess(rules, vars):
    to_del = []
    for rule_id in rules:
        rule = rules[rule_id]
        if "constraints" not in rule or "results" not in rule:
            to_del.append(rule_id)
    for rule_id in to_del:
        del rules[rule_id]
        del vars[rule_id]

    # 将时间、数量、价格改为对应的constraint表达式
    for rule_id in rules:
        rule = rules[rule_id]
        constraints = rule["constraints"]
        saved_op = ""
        to_add = []
        del_op = -1
        for pl, constraint in enumerate(constraints):
            key = constraint["key"]
            value = constraint["value"]
            if key == "op":
                saved_op = value
                del_op = pl
                continue
            # 时间
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
    
    # 修改结果，将可以、不予、不可、有效、无效、不再进行等结果改为“成功”、“失败”
    for rule_id in rules:
        rule = rules[rule_id]
        for r in rule["results"]:
            if r["value"] != "成功" and r["value"] != "不成功":
                if "不" in r["value"] or r["value"] == "无效":
                    r["value"] = "不成功"
                    r["else"] = "成功"
                else:
                    r["value"] = "成功"
                    r["else"] = "不成功"
    # 将系统“接受”、“不接受”一些操作部分改写成以会员为主语的规则
    to_add = []
    rule_id_to_add = []
    for rule_id in rules:
        rule = rules[rule_id]
        op_num = 0
        to_del = []
        ac_or_not = False  # 是不是系统为主语的接受、不接受操作
        for j, c in enumerate(rule["constraints"]):
            if c["key"] == "系统" and j not in to_del:  # 删掉"系统"
                to_del.append(j)
            elif c["key"] == "操作":
                op_num += 1
                if op_num > 1 and j not in to_del:  # 多个操作，去掉后面的所有操作
                    to_del.append(j)
                new_rule = {}
                if c["value"] == "不接受" or c["value"] == "拒绝接受":
                    ac_or_not = True
                    # 寻找对应的操作部分
                    op_part_num = 0
                    find = False
                    for i, ci in enumerate(rule["constraints"]):
                        if ci["key"] == "操作部分":
                            op_part_num += 1
                            if op_part_num == op_num:
                                # 如果有两个以上的操作是接受/不接受，需要分裂规则
                                if op_num > 1:
                                    new_rule = copy.deepcopy(rule)
                                    new_rule_id = ""
                                    old = ".".join(rule_id.split(".")[:-1])
                                    ind = int(rule_id.split(".")[-1])
                                    step = 1
                                    while step < 100000:
                                        new_rule_id = old + "." + str(ind + step)
                                        if new_rule_id not in rules and new_rule_id not in rule_id_to_add:
                                            rule_id_to_add.append(new_rule_id)
                                            break
                                        step += 1

                                    new_rule["constraints"] = []
                                    for k, ck in enumerate(rule["constraints"]):
                                        if ck["key"] == "系统" or ck["key"] == "操作" or ck["key"] == "操作部分":
                                            continue
                                        new_rule["constraints"].append(ck)
                                    if "撤销" in ci["value"]:
                                        new_rule["constraints"].append({
                                            "key":"操作",
                                            "operation":"is",
                                            "value":"撤销"
                                        })
                                    elif "申报" in ci["value"]:
                                        new_rule["constraints"].append({
                                            "key":"操作",
                                            "operation":"is",
                                            "value":"申报"
                                        })
                                else:
                                    if "撤销" in ci["value"]:
                                        c["value"] = "撤销"
                                    elif "申报" in ci["value"]:
                                        c["value"] = "申报"
                                find = True
                                break
                    if find and i not in to_del:
                        # 删掉原来的操作部分
                        to_del.append(i)
                    # 修改result为不成功
                    if "results" in new_rule and op_num > 1:
                        for r in new_rule["results"]:
                            if r["key"] == "结果":
                                r["value"] = "不成功"
                                r["else"] = "成功"
                    else:
                        for r in rule["results"]:
                            if r["key"] == "结果":
                                r["value"] = "不成功"
                                r["else"] = "成功"
                elif c["value"] == "接受":
                    ac_or_not = True
                    # 寻找对应的操作部分
                    op_part_num = 0
                    find = False
                    for i, ci in enumerate(rule["constraints"]):
                        if ci["key"] == "操作部分":
                            op_part_num += 1
                            if op_part_num == op_num:
                                # 如果有两个以上的操作是接受/不接受，需要分裂规则
                                if op_num > 1:
                                    new_rule = copy.deepcopy(rule)
                                    new_rule_id = ""
                                    old = ".".join(rule_id.split(".")[:-1])
                                    ind = int(rule_id.split(".")[-1])
                                    step = 1
                                    while step < 100000:
                                        new_rule_id = old + "." + str(ind + step)
                                        if new_rule_id not in rules and new_rule_id not in rule_id_to_add:
                                            rule_id_to_add.append(new_rule_id)
                                            break
                                        step += 1

                                    new_rule["constraints"] = []
                                    for k, ck in enumerate(rule["constraints"]):
                                        if ck["key"] == "系统" or ck["key"] == "操作" or ck["key"] == "操作部分":
                                            continue
                                        new_rule["constraints"].append(ck)
                                    if "撤销" in ci["value"]:
                                        new_rule["constraints"].append({
                                            "key":"操作",
                                            "operation":"is",
                                            "value":"撤销"
                                        })
                                    elif "申报" in ci["value"]:
                                        new_rule["constraints"].append({
                                            "key":"操作",
                                            "operation":"is",
                                            "value":"申报"
                                        })
                                else:
                                    if "撤销" in ci["value"]:
                                        c["value"] = "撤销"
                                    elif "申报" in ci["value"]:
                                        c["value"] = "申报"
                                find = True
                                break
                    if find and i not in to_del:
                        # 删掉原来的操作部分
                        to_del.append(i)
                    # 修改result为不成功
                    if "results" in new_rule and op_num > 1:
                        for r in new_rule["results"]:
                            if r["key"] == "结果":
                                r["value"] = "成功"
                                r["else"] = "不成功"
                    else:
                        for r in rule["results"]:
                            if r["key"] == "结果":
                                r["value"] = "成功"
                                r["else"] = "不成功"
                if new_rule != {}:
                    to_add.append(new_rule)
        if ac_or_not:
            to_del = sorted(to_del, reverse=True)
            for index in to_del:
                del rule["constraints"][index]
    for i, rule in enumerate(to_add):
        rules[rule_id_to_add[i]] = rule
        var = {}
        for c in rule["constraints"]:
            var[c["key"]] = []
        vars[rule_id_to_add[i]] = var
    
    # 删掉所有系统
    rule_to_del = []
    for rule_id in rules:
        rule = rules[rule_id]
        constraint_to_del = []
        for i, c in enumerate(rule['constraints']):
            if c['key'] == "系统":
                constraint_to_del.append(i)
        if len(constraint_to_del) > 0:
            for i in reversed(constraint_to_del):
                del rule['constraints'][i]
            del vars[rule_id]['系统']
        if len(rule['constraints']) == 0:
            rule_to_del.append(rule_id)
    for rule_id in rule_to_del:
        del rules[rule_id]
        del vars[rule_id]

    return rules, vars


def find_word(s, word):
        locs = [s.find(word)]
        while(locs[-1] != -1):
            locs.append(s.find(word, locs[-1] + 1))
        locs.pop()
        return locs


def time_preprocess(value):
    """
    处理“每个交易日9:15至9:30”，“在9:15前”，“在9:30后”等时间语句表达
    如果是合法的时间表达，返回True, R规则表示的时间
    否则，返回False, 非法原因
    """
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
        # 考虑三种时间的情况，9:00至10:00，9:00后，9:00前，其他情况直接照抄
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
                    t += f"[00:00-{time_vals[p]}],"
                    p += 1
                else:
                    valid = False
                    break
            else:  # loc in loc_3s
                vl = vals_locs[p]
                if vl < loc:
                    t += f"[{time_vals[p]}-24:00],"
                    p += 1
                else:
                    valid = False
                    break
        if valid:
            t = t[:-1] + "}"
            return True, t
        else:
            return False, f"非法的时间表达: \"{value}\""
    return False, f"\"{value}\"中不含有时间表达"

def judge_op(value):
    value = value.replace("得", "")
    
    if "不低于" in value or "达到" in value or "以上" in value:
        return ">="
    if "不高于" in value or "以下" in value or "不超过" in value or "以内" in value:
        return "<="
    if "低于" in value or "未达到" in value or "不足" in value or "小于" in value:
        return "<"
    if "高于" in value or "超过" in value or "优于" in value or "大于" in value:
        return ">"
    if "等于" in value or "为" in value:
        return "=="
    if "不等于" in value:
        return "!="
    return ""


def num_preprocess(value):
    """
    处理“1000元或者其整数倍”，“大于1000元”等时间表达
    如果合法，返回True, 数量的R规则表达
    否则，返回False, 非法原因
    """
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
        while(unit_loc < len(v) and (v[unit_loc] == "亿" or v[unit_loc] == "万")):
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
        return False, f"句子\"{v}\"中没有合法约束"
    return True, t



def price_preprocess(value):
    price_re = r"\d+\.\d+|\d+"
    price_vals = re.findall(price_re, value)
    if len(price_vals) == 1:
        if value.find(price_vals[0]) == 0:
            return True, ["==", price_vals[0]]
        else:
            num_val = price_vals[0]
            v = value
            val_loc = v.find(num_val)
            unit_loc = val_loc + len(num_val)
            while(unit_loc < len(v) and (v[unit_loc] == "亿" or v[unit_loc] == "万")):
                if v[unit_loc] == "万":
                    num_val += "0000"
                elif v[unit_loc] == "亿":
                    num_val += "00000000"
                unit_loc += 1
            op = judge_op(v)
            if op != "":
                return True, [op, num_val]
            else:
                return False, ""
    else:
        return False, ""



def compose_rules_r1_r2(defines, vars, rules, preliminaries, rule_name = "rule"):
    """
    规则组合函数, 包含:
    1. 组合明显嵌套的规则
    2. 补全单规则相关的字段
    3. 将规则中的时间替换为具体的时间（开盘集合匹配阶段）
    4. 补全"其他"交易方式等
    5. 申报数量<100...0和其他规则的组合, 同一rule下subrule的组合
    6. 除本规则规定的不接受撤销申报的时间段外，其他接受申报的时间内怎样怎样
    7. 没有then就删掉，这是另一个去重步
    """
    # 组合明显嵌套的规则
    vars, rules = compose_nested_rules(vars, rules)
    # 必须交易阶段相同，一个是订单连续性操作，一个是交易时间，组合
    vars, rules = compose_same_stage(vars, rules)
    # "其他"补全
    vars, rules = supply_other_rules(vars, rules, preliminaries)

    # 统一规则下的子规则组合，申报数量<100...0和其他规则的组合
    vars, rules = subrule_compose(vars, rules)
    
    # 补全单规则相关的字段
    vars, rules = supply_rules_on_prelim(defines, vars, rules, preliminaries)

    # 除本规则规定的不接受撤销申报的时间段外，其他接受申报的时间内怎样怎样
    vars, rules = compute_other_time_in_rules(vars, rules, preliminaries)
    # 没有then就删掉
    vars, rules = delete_then(vars, rules)

    # 添加操作，如果一条规则没有操作，操作为“申报”
    vars, rules = add_operation(vars, rules)


    # 打印中间结果
    # with open(f"rules/r2_{rule_name}.txt", "w", encoding="utf-8") as f:
    #     f.write(pprint.pformat(rules))
    # print(f"R2包含的规则数：{len(vars.keys())}")
    
    return defines, vars, rules









def judge_rule_conflict(rule1, rule2):
    for c1 in rule1['constraints']:
        conflict = False
        for c2 in rule2['constraints']:
            if c1['key'] == c2['key']:
                if c1['value'] == c2['value']:
                    conflict = False
                    break
                else:
                    conflict = True
        if conflict:
            return True
    return False


def compose_nested_rules(vars, rules):
    # 遍历，找到所有结合规则
    rule_to_del = []
    for rule_id in list(rules.keys()):
        rule = rules[rule_id]
        var = vars[rule_id]
        for c in rule['constraints']:
            if c['key'] == '结合规则':
                rule_to_del.append(rule_id)
                loc1 = c['value'].find("第")
                loc2 = c['value'].find("条")
                # 找到要结合的规则的id
                compose_rule_id = c['value'][loc1+1:loc2]
                # 找到要结合的规则，要求不互相冲突
                for rule_id1 in list(rules.keys()):
                    if compose_rule_id in rules[rule_id1]['rule_class'] and not judge_rule_conflict(rule, rules[rule_id1]):
                        # 构建结合后的规则
                        new_rule = {
                            "constraints": copy.deepcopy(rules[rule_id1]['constraints']),
                            "focus": list(set(rule['focus'] + rules[rule_id1]['focus'])),
                            "results": copy.deepcopy(rule['results']),
                            "rule_class": list(set(rule['rule_class'] + rules[rule_id1]['rule_class']))
                        }
                        for ci in rule['constraints']:
                            if ci not in new_rule['constraints'] and ci['key'] != "结合规则":
                                new_rule['constraints'].append(ci)
                        new_id = rule_id + "," + rule_id1
                        rules[new_id] = new_rule
                        var = {}
                        for ci in new_rule['constraints']:
                            var[ci['key']] = []
                        vars[new_id] = var

    for rule_id in rule_to_del:
        del rules[rule_id]
        del vars[rule_id]

    return vars, rules



def construct_tree(preliminaries, jypz):
    arr = []
    for key in list(preliminaries.keys()):
        if "交易方式" in key and jypz in key:
            for value in preliminaries[key]:
                arr.append(["交易方式", value])
    end = False
    while not end:
        end = True
        new_arr = []
        for kv in arr:
            father_key, father_value = kv[-2], kv[-1]
            add_old_kv = True
            arr_local = []
            for key in list(preliminaries.keys()):
                # 大宗交易 必须在 大宗交易交易方式 的开头才行
                if (key.find(father_value) == 0 or len(kv)>=4 and key.find(kv[-3])==0 and father_value in key) and isinstance(preliminaries[key], list):
                    # 如果当前要添加的key、value已存在，跳过
                    if key in kv:
                        continue
                    find = False
                    for value in preliminaries[key]:
                        if value in kv:
                            find = True
                            break
                    if find:
                        continue
                    
                    # 添加
                    if len(arr_local) == 0:
                        if "指令" in key or "要素" in key or "内容" in key:
                            if len(kv)>=4 and key.find(kv[-3])==0 and father_value in key:
                                arr_local.append(copy.deepcopy(kv) + [key, ",".join(preliminaries[key])])
                                end = False
                                add_old_kv = False
                        else:
                            for value in preliminaries[key]:
                                new_kv = copy.deepcopy(kv)
                                new_kv += [key, value]
                                arr_local.append(new_kv)
                            end = False
                            add_old_kv = False
                    else:
                        if "指令" in key or "要素" in key or "内容" in key:
                            
                            if len(kv)>=4 and key.find(kv[-3])==0 and father_value in key:
                                for kv1 in arr_local:
                                    kv1 += [key, ",".join(preliminaries[key])]
                                end = False
                                add_old_kv = False
                        else:
                            a = []
                            multi_num = len(preliminaries[key])
                            for _ in range(multi_num):
                                a += copy.deepcopy(arr_local)
                            arr_local = a
                            
                            for i, value in enumerate(preliminaries[key]):
                                for kvi in arr_local[int(len(arr_local)/multi_num*i):int(len(arr_local)/multi_num*(i+1))]:
                                    kvi += [key, value]
                            end = False
                            add_old_kv = False
                    
            if add_old_kv:
                arr_local.append(kv)
            new_arr += arr_local
        arr = copy.deepcopy(new_arr)
    # pprint.pprint(arr)
    return arr



def supply_rules_on_prelim(defines, vars, rules, preliminaries):
    # 如果规则中没有"单独可测试规则要素"，添加
    elements = preliminaries["单独可测试规则要素"]
    tree = {}
    beside_key = ["交易品种", "操作", "操作部分", "事件", "状态", "操作人", "条件", "结合规则"]

    for element in elements:
        if element == "交易方向":
            # 交易操作
            to_delete = []
            for rule_id in list(rules.keys()):
                index = 1
                rule = rules[rule_id]
                find = False
                for c in rule['constraints']:
                    if c['key'] == '操作':  # 认购(买)、申购(买)、赎回(卖)、申购(买卖)、竞买(卖)、应价(买)
                        if '买入' in c['value'] or "认购" in c['value'] or "申购" in c['value'] or "应价" in c['value']:
                            rule['constraints'].append({"key":"交易方向","operation":"is","value":"买入"})
                            vars[rule_id]['交易方向'] = []
                            find = True
                            break
                        if '卖出' in c['value'] or "赎回" in c['value'] or "竞买" in c['value']:
                            rule['constraints'].append({"key":"交易方向","operation":"is","value":"卖出"})
                            vars[rule_id]['交易方向'] = []
                            find = True
                            break
                if not find:
                    to_delete.append(rule_id)
                    for direction in preliminaries[element]:
                        new_rule = copy.deepcopy(rule)
                        new_var = copy.deepcopy(vars[rule_id])
                        new_rule['constraints'].append({"key":element, "operation":"is", "value":direction})
                        new_var[element] = []
                        rules[f"{rule_id}.{index}"] = new_rule
                        vars[f"{rule_id}.{index}"] = new_var
                        index += 1
            for rule_id in to_delete:
                del vars[rule_id]
                del rules[rule_id]
        if element in defines:  # 交易品种/交易市场
            e = defines[element][0]
            if e == "证券":
                e = preliminaries['交易品种']
            to_delete = []
            for rule_id in list(rules.keys()):
                rule = rules[rule_id]
                find = False
                jypz = ""
                for c in rule['constraints']:
                    if c['key'] == element:  # 只有交易品种才可能走这个分支
                        jypz = c['value']
                        new_jypz = ""
                        if "创业" in jypz:
                            new_jypz = "创业板"
                        else:
                            if "债" in jypz:
                                new_jypz = "债券"
                            if "股" in jypz:
                                new_jypz = "股票"
                            if "基金" in jypz or "ET" in jypz or "TF" in jypz or "LO" in jypz or "OF" in jypz:
                                new_jypz = "基金"
                            if new_jypz == "":
                                new_jypz = jypz
                        if jypz != new_jypz:
                            c['value'] = new_jypz
                            rule['constraints'].append({"key":f"{new_jypz}品种", "operation":"is", "value":jypz})
                            vars[rule_id][f"{new_jypz}品种"] = []
                        find = True
                        break
                if not find or jypz == "证券":
                    if jypz == "证券":
                        e = preliminaries['交易品种']
                    if isinstance(e, str):
                        rule['constraints'].append({"key":element, "operation":"is", "value":e})
                        vars[rule_id][element] = []
                    elif isinstance(e, list):
                        for eidx, ei in enumerate(e):
                            new_id = f"{rule_id}.{eidx+1}"
                            new_rule = copy.deepcopy(rule)
                            if jypz == "证券":
                                for c in new_rule['constraints']:
                                    if c['key'] == element:
                                        c['value'] = ei
                            else:
                                new_rule['constraints'].append({"key":element, "operation":"is", "value":ei})
                            rules[new_id] = new_rule
                            new_var = copy.deepcopy(vars[rule_id])
                            new_var[element] = []
                            vars[new_id] = new_var
                        to_delete.append(rule_id)
            for rule_id in to_delete:
                del rules[rule_id]
                del vars[rule_id]
        if element == "交易方式":
            # 获取交易品种，得到对应的交易方式，填入
            to_delete = []
            for rule_id in list(rules.keys()):
                rule = rules[rule_id]
                # 查找交易品种
                for c in rule['constraints']:
                    if c['key'] == "交易品种":
                        jypz = c['value']
                        new_jypz = ""
                        if "创业" in jypz:
                            new_jypz = "创业板"
                        else:
                            if "债" in jypz:
                                new_jypz = "债券"
                            if "股" in jypz:
                                new_jypz = "股票"
                            if "基金" in jypz or "ET" in jypz or "TF" in jypz or "LO" in jypz or "OF" in jypz:
                                new_jypz = "基金"
                            if new_jypz == "":
                                new_jypz = jypz
                        jypz = new_jypz
                        break
                if jypz in tree:
                    tree_local = tree[jypz]
                else:
                    tree_local = construct_tree(preliminaries, jypz)
                    tree[jypz] = tree_local
                index = 1
                # 将ti加入rule['constraints']中
                for ti in tree_local:
                    new_rule = copy.deepcopy(rule)
                    new_var = copy.deepcopy(vars[rule_id])
                    conflict = False
                    for i in range(0, len(ti), 2):
                        find_value = False
                        find_key = False
                        for c in rule['constraints']:
                            if c['value'] == ti[i+1]:
                                find_value = True
                                break
                            if c['key'] == ti[i]:
                                find_key = True
                        if find_value:  # 找到了相同的value，这个value就不用加了
                            continue
                        if find_key:  # 找到了key，但value不同，冲突，这个ti不继续加了
                            conflict = True
                            break
                        # 将value加入规则中
                        new_rule['constraints'].append({"key": ti[i], "operation": "is", "value": ti[i+1]})
                        new_var[ti[i]] = []
                    if not conflict:
                        new_id = f"{rule_id}.{index}"
                        index += 1
                        rules[new_id] = new_rule
                        vars[new_id] = new_var
                        if rule_id not in to_delete:
                            to_delete.append(rule_id)
            for id in to_delete:
                del rules[id]
                del vars[id]
    
    return vars, rules




def compose_same_stage(vars, rules):
    rule_to_delete = []
    for i, rule_id1 in enumerate(list(rules.keys())):
        rule1 = rules[rule_id1]
        new_rule = copy.deepcopy(rule1)
        new_id = rule_id1
        for idx, c1 in enumerate(rule1['constraints']):
            if c1['key'] == "时间" and c1['operation'] == "is":
                time_key = c1['value']
                if "阶段" in time_key:
                    time_key = time_key[:time_key.find("阶段")]
                if "时间" in time_key:
                    time_key = time_key[:time_key.find("时间")]

                for j, rule_id2 in enumerate(rules):
                    if i == j:
                        continue
                    rule2 = rules[rule_id2]
                    find = False
                    for c2 in rule2['constraints']:
                        if time_key in c2['key']:
                            new_rule['constraints'][idx]['operation'] = "in"
                            new_rule['constraints'][idx]['value'] = copy.deepcopy(c2['value'])
                            new_rule['focus'] = list(set(new_rule['focus'] + rule2['focus']))
                            new_rule['rule_class'] = list(set(new_rule['rule_class'] + rule2['rule_class']))
                            if rule_id2 not in new_id.split(","):
                                new_id += "," + rule_id2
                            find = True
                            break
                    if find:
                        break
        
        if new_id != rule_id1:
            rules[new_id] = new_rule
            var = copy.deepcopy(vars[rule_id1])
            vars[new_id] = var
            rule_to_delete.append(rule_id1)

    for rule_id in rule_to_delete:
        del rules[rule_id]
        del vars[rule_id]
    return vars, rules





def supply_other_rules(vars, rules, preliminaries):
    to_delete = []
    keys = list(vars.keys())
    for rule_id in keys:
        rule = rules[rule_id]
        for c in rule["constraints"]:
            if "其他" in c["value"]:  # 其他申报类型
                want = c['value'][c['value'].find("其他")+2:]
                # 将已有c['key']的同一rule_class下的c['value']挑选出来
                have = []
                rule_class = rule["rule_class"]
                for rule_id1 in keys:
                    if rule_class == rules[rule_id1]["rule_class"] and rule_id != rule_id1:
                        for c0 in rules[rule_id1]["constraints"]:
                            if c0['key'] == c["key"] and c0['value'] != c["value"] and c0["value"] not in have:
                                have.append(c0["value"])
                                break
                # 取反
                if want not in preliminaries:
                    continue
                c_key = preliminaries[want]
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
                    # 时间
                    if c['operation'] == "in":
                        conflict = True
                        break
                    # 少于...一次性申报
                    if c['key'] == "操作" and "一次性" in c['value']:
                        conflict = True
                        break
                    find = False
                    for c1 in new_rule["constraints"]:
                        if c1['operation'] == "in":
                            conflict = True
                            break
                        if(c1['key'] == "操作" and "一次性" in c1['value']):
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
# '3.3.12.1.1.1': {'constraints': [{'key': '时间',
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

def add_operation(vars, rules):
    keys = list(rules.keys())
    for rule_id in keys:
        have_op = False
        value_constraint = False
        rule = rules[rule_id]
        for c in rule['constraints']:
            if c['key'] == '操作':
                have_op = True
                break
            if is_time_key(c['key']) or is_num_key(c['key']) or is_price_key(c['key']):
                value_constraint = True
        if not have_op and value_constraint:
            rule['constraints'].append({"key":"操作","operation":"is","value":"申报"})
            vars[rule_id]['操作'] = []
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








import json
import pprint
import copy
import hanlp
from ours.process_tci_to_tco import token_classification
from ours.process_tco_to_r1 import to_r1

HanLP = hanlp.load(hanlp.pretrained.mtl.CLOSE_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_SMALL_ZH)

def compose_rules_r2_r3(defines, vars, rules, preliminaries, rule_name = 'rule'):
    """
    r2到r3的转换
    1. 结合状态机
    2. 添加一些预定义的要素
    """
    # 增加关联标记
    for rule_id in list(rules.keys()):
        rule = rules[rule_id]
        rule['before'] = []
        rule['after'] = []

    # 处理事件
    # 对于...前，直到...等情况，会生成一条反例规则，例如在A前做B可以成功，生成反例为A后做B失败
    # 这里不生成两条规则，是因为B才是动作的重点，A做不做都可以。
    # 对于...后，...的等情况，会生成两条相关联的规则，例如做A后做B成功，可以生成做A成功，A之后做B成功。
    vars, rules = deal_with_event(vars, rules)

    # 结合状态机
    vars, rules = compose_state_machine(vars, rules, preliminaries)

    # 添加一些预定义的要素
    # vars, rules = add_elements(vars, rules, preliminaries)

    # 打印中间结果
    # with open(f"rules/r3_{rule_name}.txt", "w", encoding="utf-8") as f:
    #     f.write(pprint.pformat(rules))
    # print(f"R3包含的规则数：{len(rules.keys())}")

    return defines, vars, rules



def deal_with_event_precond(event):
    pos= HanLP(event,tasks='pos')

    tok = pos["tok/fine"]
    ctb = pos["pos/ctb"]

    keys, values = [], []
    n, v = "", ""
    last = ""
    # print(tok, ctb)
    for i, c in enumerate(ctb):
        t = tok[i]
        if c == "VV":
            if last == "VV":
                v += t
                continue
            elif last == "NN":
                if n == "本所":
                    keys.append("系统")
                elif n == "会员" or n == "对手方":
                    keys.append("操作人")
                else:
                    keys.append("操作部分")
                values.append(n)
                n = ""
            v += t
        elif c == "NN" or c == "NT":
            if last == "DT":
                n += tok[i-1]
            if last == "NN" or last == "NT":
                n += t
                continue
            elif last == "VV":
                if v != "盘":
                    keys.append("操作")
                    values.append(v)
                v = ""
            n += t
        elif c != last:
            if v != "":
                if c != "DEC" and v != "盘":
                    keys.append("操作")
                    values.append(v)
                v = ""
            if n != "":
                if n == "本所":
                    keys.append("系统")
                elif n == "会员" or n == "对手方":
                    keys.append("操作人")
                else:
                    keys.append("操作部分")
                values.append(n)
                n = ""
        last = c
    if n != "":
        if n == "本所":
            keys.append("系统")
        elif n == "会员" or n == "对手方":
            keys.append("操作人")
        else:
            keys.append("操作部分")
        values.append(n)
    if v != "":
        keys.append("操作")
        values.append(v)
    return keys, values

    # if event[-1] != "。":
    #     event = event + "。"
    # tci = [
    #     {
    #         "id":"1.1.1",
    #         "text":event,
    #         "label":""
    #     }
    # ]
    # knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    # tco = token_classification(tci, knowledge, "../model/ours/best_1701809213", "../data/tc_data.dict")
    # # 当日额度在本所盘后定价交易阶段使用完毕的
    # r1 = to_r1(tco, knowledge)
    # print(r1)
    # return [], []



def deal_with_event(vars, rules):

    rule_to_add = []
    rule_id_to_add = []
    rule_id_to_del = []
    for rule_id in rules:
        rule = rules[rule_id]
        constraints = rule["constraints"]
        add_origin_rule = False  # 在处理...后的所有情况后，将原规则也添加上去
        for constraint in constraints:
            if constraint["key"] == "事件":
                event = constraint["value"]
                events = event.split(",")
                for event in events:
                    if event[-1] == "前" or "直到" in event:
                        # 前的处理，将“前”变成“后”，并将结果反转
                        # rule: 在A前，做B，成功
                        # new_rule: A后，做B，失败
                        rule_id_to_del.append(rule_id)
                        rule_to_add.append(rule)
                        rule_id_to_add.append(rule_id + ".1")
                        new_rule = copy.deepcopy(rule)
                        new_rule_id = rule_id + ".2"
                        for c in new_rule["constraints"]:
                            if c["key"] == "事件":
                                c["value"] = c["value"].replace("前", "后")
                                break
                        for r in new_rule["results"]:
                            if r["key"] == "结果":
                                rv = r["value"]
                                r["value"] = r["else"]
                                r["else"] = rv
                                break
                        rule_to_add.append(new_rule)
                        rule_id_to_add.append(new_rule_id)
                    else:  # “后”，并将默认情况看作“后”
                        # 提取事件中的操作、操作人、操作部分，并将其写为一条前置规则
                        keys, values = deal_with_event_precond(event)
                        new_rule = {}
                        new_rule["rule_class"] = copy.deepcopy(rule["rule_class"])
                        new_rule["focus"] = copy.deepcopy(rule["focus"])
                        new_rule["results"] = [{
                            "key":"结果",
                            "operation":"is",
                            "value":"成功",
                            "else":"不成功"
                        }]
                        new_rule['before'] = []
                        new_rule['after'] = []
                        new_rule["constraints"] = []
                        # 事件前的约束
                        for c in rule["constraints"]:
                            if c["key"] == "事件":
                                break
                            new_rule["constraints"].append(copy.deepcopy(c))
                        new_rules = [new_rule]
                        
                        for i, key in enumerate(keys):
                            value = values[i]
                            # example: 经纪客户委托会员申报
                            if i > 0 and (key == "系统" or key == "操作人") and keys[i-1] == "操作":
                                # 直接分裂
                                rule_to_add_1 = []
                                for new_rule in new_rules:
                                    new_rule_cp = copy.deepcopy(new_rule)
                                    new_rule_cp["constraints"] = []
                                    for c in new_rule["constraints"]:
                                        if c["key"] == "操作" or c["key"] == "操作部分" or c["key"] == key:
                                            break
                                        new_rule_cp["constraints"].append(c)
                                    new_rule_cp["constraints"].append({
                                        "key": key,
                                        "operation": "is",
                                        "value": value
                                    })
                                    rule_to_add_1.append(new_rule_cp)
                                new_rules += rule_to_add_1
                            else:  # 其他约束，不冲突就加上
                                rule_to_add_1 = []
                                if_add = False
                                for new_rule in new_rules:
                                    conflict = False
                                    for c in new_rule["constraints"]:
                                        if c["key"] == key:
                                            conflict = True
                                            break
                                    if not conflict:
                                        new_rule["constraints"].append({
                                            "key":key,
                                            "operation":"is",
                                            "value":value
                                        })
                                        if_add = True
                                if not if_add:  # 已有的没有规则能加上的，新建规则
                                    for new_rule in new_rules:
                                        new_rule_cp = copy.deepcopy(new_rule)
                                        new_rule_cp["constraints"] = []
                                        for c in new_rule["constraints"]:
                                            if c["key"] == key:
                                                break
                                            new_rule_cp["constraints"].append(c)
                                        new_rule_cp["constraints"].append({
                                            "key":key,
                                            "operation":"is",
                                            "value":value
                                        })
                                        rule_to_add_1.append(new_rule_cp)
                                new_rules += rule_to_add_1
                        rule_id_to_del.append(rule_id)
                        rule_to_add += [new_rule for new_rule in new_rules if len(new_rule['constraints'])>0]
                        add_origin_rule = True
                        add_i = 1
                        for i in range(len(new_rules)):
                            while f"{rule_id}.{i+add_i}" in rule_id_to_add:
                                add_i += 1
                            rule_id_to_add.append(f"{rule_id}.{i+add_i}")

        if add_origin_rule:
            rule_to_add.append(copy.deepcopy(rule))
            add_i=1
            while f"{rule_id}.{add_i}" in rule_id_to_add:
                add_i += 1
            rule_id_to_add.append(f"{rule_id}.{add_i}")



    for rule_id in rule_id_to_del:
        if rule_id in rules:
            del rules[rule_id]
            del vars[rule_id]
    last_id = ""
    for i, rule in enumerate(rule_to_add):
        rule_id = rule_id_to_add[i]
        if last_id != "":
            rules[last_id]['after'].append(rule_id)
            rule['before'].append(last_id)
        rules[rule_id] = rule
        last_id = rule_id
        var = {}
        for c in rule["constraints"]:
            if c["key"] not in var:
                var[c["key"]] = []
        vars[rule_id] = var

    return vars, rules



def op_match(trigger, operation, op_part):
    if "撤销" in trigger and "撤销" in operation:
        if trigger.replace("撤销", "") in operation.replace("撤销", "") or operation.replace("撤销", "") in trigger.replace("撤销", ""):
            return True
    elif "撤销" in trigger or "撤销" in operation:
        return False
    elif trigger in operation or operation in trigger:
        return True
    elif "提交" in operation and trigger in op_part:
        return True
    else:
        return False


def compose_state_machine(vars, rules, preliminaries):
    # 结合状态机的想法就是，去匹配操作，如果规则中的操作和状态机的操作相同
    # 就将订单状态加到constraints和results中

    # preliminaries = json.load(open("preliminaries.json", "r", encoding="utf-8"))
    state_machines = preliminaries["stateMachine"]
    
    to_delete = []
    to_add = {}

    keys = list(rules.keys())
    for rule_id in keys:
        rule = rules[rule_id]
        # 只去匹配第一个操作和操作部分
        operation = ""
        op_part = ""
        for c in rule['constraints']:
            if c['key'] == '操作':
                operation = c['value']
            if c["key"] == "操作部分":
                op_part = c["value"]
            if operation != "" and op_part != "":
                break
        if operation == "":
            continue
        new_rule_number = 1
        for state_machine in state_machines:
            key = state_machine['state_name']  # 要添加的key
            cnts = state_machine['transition']
            for x, cnt in enumerate(cnts):
                reject = False
                trigger = cnt['trigger']
                if '失败' in cnt['trigger']:
                    reject = True
                    trigger = cnt['trigger'][:-2]
                if op_match(trigger, operation, op_part):  # 操作相同
                    compose = False
                    if reject:
                        # 这里是失败，所以not_acc也必须是失败
                        for r in rule['results']:
                            if r["key"] == "结果" and r['value'] == "不成功":
                                compose = True
                                break
                    else:
                        # 这里是成功，所以result也必须是成功
                        for r in rule['results']:
                            if r["key"] == "结果" and r['value'] == "成功":
                                compose = True
                                break
                    if not compose:
                        continue
                    # 添加状态机
                    new_id = rule_id + "," + str(new_rule_number)
                    new_rule_number += 1
                    new_rule = copy.deepcopy(rule)
                    new_rule['constraints'].append({"key":key,"operation":"is","value":cnt['from']})
                    new_rule['results'].append({"key":key,"operation":"is","value":cnt['to']})
                    to_add[new_id] = new_rule
                    if rule_id not in to_delete:
                        to_delete.append(rule_id)
                    vars[new_id] = copy.deepcopy(vars[rule_id])
                    vars[new_id][key] = []

    for id in to_delete:
        del vars[id]
        del rules[id]
    new_keys = list(to_add.keys())
    for id in new_keys:
        rules[id] = to_add[id]

    rules = add_relation(rules)

    return vars, rules


def add_relation(rules):
    # 对于所有规则两两观察是否有一条规则在result有状态，另一条规则在consstraint有状态，且二者相等，有的话就关联。
    keys = list(rules.keys())
    from_states, to_states = {}, {}
    for rule_id in keys:
        rule = rules[rule_id]
        from_state, to_state = [], []
        for c in rule['constraints']:
            if c['key'] == "状态":
                from_state.append(c['value'])
        for r in rule['results']:
            if r['key'] == "状态":
                to_state.append(r['value'])
        from_states[rule_id] = from_state
        to_states[rule_id] = to_state
    for i, rule_id1 in enumerate(keys):
        from_state1, to_state1 = from_states[rule_id1], to_states[rule_id1]
        if len(from_state1) == 0 and len(to_state1) == 0:
            continue
        for j, rule_id2 in enumerate(keys):
            from_state2, to_state2 = from_states[rule_id2], to_states[rule_id2]
            if j <= i or len(from_state2) == 0 and len(to_state2) == 0:
                continue
            for s1 in from_state1:
                for t2 in to_state2:
                    if s1 == t2 or ("撤销" not in s1 and "撤销" not in t2 and (s1 in t2 or t2 in s1)) or ("撤销" in s1 and "撤销" in t2 and (s1.replace("撤销", "") in t2.replace("撤销", "") or t2.replace("撤销", "") in s1.replace("撤销", ""))):  # 状态相同
                        # rule2 -> rule1
                        for xi in rules[rule_id2]['after']:
                            if xi in rule_id1:
                                rules[rule_id2]['after'].remove(xi)
                        rules[rule_id2]['after'].append(rule_id1)
                        for xi in rules[rule_id1]['before']:
                            if xi in rule_id2:
                                rules[rule_id1]['before'].remove(xi)
                        rules[rule_id1]['before'].append(rule_id2)
            for s2 in from_state2:
                for t1 in to_state1:
                    if s2 == t1 or ("撤销" not in s2 and "撤销" not in t1 and (s2 in t1 or t1 in s2)) or ("撤销" in s2 and "撤销" in t1 and (s2.replace("撤销", "") in t1.replace("撤销", "") or t1.replace("撤销", "") in s2.replace("撤销", ""))):  # 状态相同
                        # rule1 -> rule2
                        for xi in rules[rule_id2]['before']:
                            if xi in rule_id1:
                                rules[rule_id2]['before'].remove(xi)
                        rules[rule_id2]['before'].append(rule_id1)
                        for xi in rules[rule_id1]['after']:
                            if xi in rule_id2:
                                rules[rule_id1]['after'].remove(xi)
                        rules[rule_id1]['after'].append(rule_id2)
    
    for rule_id in keys:
        rule = rules[rule_id]
        if len(rule['after']) > 0:
            restart = True
            while restart:
                restart = False
                for i, t in enumerate(rule['after']):
                    if t not in keys:
                        to_add = [id1 for id1 in keys if t in id1]
                        del rule['after'][i]
                        rule['after'] += to_add
                        restart = True
                        break
        if len(rule['before']) > 0:
            restart = True
            while restart:
                restart = False
                for i, t in enumerate(rule['before']):
                    if t not in keys:
                        to_add = [id1 for id1 in keys if t in id1]
                        del rule['before'][i]
                        rule['before'] += to_add
                        restart = True
                        break
    return rules


def add_elements(vars, rules, preliminaries):
    # 主要包含两个：
    # 1. 添加匹配成交的申报类型为限价申报，以及限价申报要素
    # 2. 添加应价申报要素

    # preliminaries = json.load(open("preliminaries.json", "r", encoding="utf-8"))
    # 添加申报类型
    prelim_keys = list(preliminaries.keys())
    rule_keys = list(rules.keys())
    rule_id_to_del = []
    for key in prelim_keys:
        if '申报类型' in key:
            transaction_mode = key[:-4]
            for rule_id in rule_keys:
                rule = rules[rule_id]
                has_clt = False
                for c in rule["constraints"]:
                    if "申报类型" in c["key"]:
                        has_clt = True
                        break
                if has_clt:
                    continue
                for c in rule['constraints']:
                    if isinstance(c['value'], str) and c['value'] in transaction_mode and isinstance(preliminaries[key], list):
                        rule_id_to_del.append(rule_id)
                        i = 1
                        for v in preliminaries[key]:
                            if "其他" in v:
                                continue
                            new_rule_id = rule_id + "." + str(i)
                            i += 1
                            new_rule = copy.deepcopy(rule)
                            new_rule['constraints'].append({"key":"申报类型","operation":"is","value":v})
                            rules[new_rule_id] = new_rule
                            vars[new_rule_id] = copy.deepcopy(vars[rule_id])
                            vars[new_rule_id]['申报类型'] = []
                        break
    for rule_id in rule_id_to_del:
        if rule_id in rules:
            del rules[rule_id]
        if rule_id in vars:
            del vars[rule_id]
    
    rule_keys = list(rules.keys())
    # 添加申报要素
    for key in prelim_keys:
        if '申报要素' in key:
            declaration_type = key[:-4]
            for rule_id in rule_keys:
                rule = rules[rule_id]
                has_clt = False
                for c in rule["constraints"]:
                    if "申报要素" in c["key"]:
                        has_clt = True
                        break
                if has_clt:
                    continue
                operator_in, operation_in, others_in = False, False, False
                for c in rule['constraints']:
                    if isinstance(c['value'], str) and c['value'] in declaration_type:
                        if c['key'] == '操作人':
                            operator_in = True
                        elif c['key'] == '操作' or c['key'] == "操作部分":
                            operation_in = True
                        else:
                            others_in = True
                        if operator_in and operation_in or others_in:
                            elements = preliminaries[key]
                            element_str = "、".join(elements)
                            rule['constraints'].append({"key":"申报要素","operation":"is","value":element_str})
                            vars[rule_id]["申报要素"] = []
                        break
    


    return vars, rules





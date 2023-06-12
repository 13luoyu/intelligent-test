import json
import pprint
import copy
import hanlp

HanLP = hanlp.load(hanlp.pretrained.mtl.CLOSE_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_SMALL_ZH)

def compose_rules_r2_r3(defines, vars, rules, preliminaries, rule_name = 'rule'):
    """
    r2到r3的转换
    1. 结合状态机
    2. 添加一些预定义的要素
    """

    # 结合状态机
    # vars, rules = compose_state_machine(vars, rules, preliminaries)

    # 处理事件
    vars, rules = deal_with_event(vars, rules)

    # 添加一些预定义的要素
    vars, rules = add_elements(vars, rules, preliminaries)

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
        elif c == "NN":
            if last == "DT":
                n += tok[i-1]
            if last == "NN":
                n += t
                continue
            elif last == "VV":
                keys.append("操作")
                values.append(v)
                v = ""
            n += t
        elif c != last:
            if v != "":
                if c != "DEC":
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



def deal_with_event(vars, rules):

    rule_to_add = []
    rule_id_to_add = []
    rule_id_to_del = []
    for rule_id in rules:
        rule = rules[rule_id]
        constraints = rule["constraints"]
        for constraint in constraints:
            if constraint["key"] == "事件":
                event = constraint["value"]
                events = event.split(",")
                for event in events:
                    if event[-1] == "前" or "直到" in event:
                        # 前的处理，将“前”变成“后”，并将结果反转
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
                        new_rule["results"] = copy.deepcopy(rule["results"])  # 也可以不复制直接写
                        new_rule["constraints"] = []
                        for c in rule["constraints"]:
                            if c["key"] == "事件":
                                break
                            new_rule["constraints"].append(copy.deepcopy(c))
                        new_rules = [new_rule]
                        for i, key in enumerate(keys):
                            value = values[i]
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
                            else:
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
                                if not if_add:
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
                        rule_to_add += new_rules
                        rule_to_add.append(rule)
                        add_i = 1
                        for i in range(len(new_rules) + 1):
                            while f"{rule_id}.{i+add_i}" in rule_id_to_add:
                                add_i += 1
                            rule_id_to_add.append(f"{rule_id}.{i+add_i}")




    for rule_id in rule_id_to_del:
        if rule_id in rules:
            del rules[rule_id]
            del vars[rule_id]
    for i, rule in enumerate(rule_to_add):
        rule_id = rule_id_to_add[i]
        rules[rule_id] = rule
        var = {}
        for c in rule["constraints"]:
            if c["key"] not in var:
                var[c["key"]] = []
        vars[rule_id] = var

    return vars, rules






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
        operation = ""
        transaction_mode = ""
        transaction_variety = ""
        for c in rule['constraints']:
            if c['key'] == '操作':
                operation = c['value']
            if c['key'] == "交易方式":
                transaction_mode = c['value']
            if c['key'] == "交易品种":
                transaction_variety = c['value']
        if operation == "":
            continue
        new_rule_number = 1
        for state_machine in state_machines:
            if transaction_mode in state_machine['name'] or transaction_variety in state_machine['name']:
                key = state_machine['state_name']  # 要添加的key
                cnts = state_machine['transition']
                for x, cnt in enumerate(cnts):
                    not_acc = ""
                    trigger = cnt['trigger']
                    if '失败' in cnt['trigger']:
                        not_acc = cnt['trigger'][-2:]
                        trigger = cnt['trigger'][:-2]
                    if trigger == operation:  # 操作相同
                        compose = False
                        # 这里要特殊处理一种，就是操作不接受的情况
                        if not_acc != "":
                            for r in rule['results']:
                                if r['value'] == not_acc:
                                    compose = True
                                    break
                        else:
                            # 这里是成功，所以result也必须是成功
                            exist = False
                            for r in rule['results']:
                                if '不' in r['value']:
                                    exist = True
                                    break
                            if not exist:
                                compose = True
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


    return vars, rules



def add_elements(vars, rules, preliminaries):
    # 主要包含两个：
    # 1. 添加匹配成交的申报类型为限价申报，以及限价申报要素
    # 2. 添加应价申报要素

    # preliminaries = json.load(open("preliminaries.json", "r", encoding="utf-8"))
    # 添加申报类型
    prelim_keys = list(preliminaries.keys())
    rule_keys = list(rules.keys())
    for key in prelim_keys:
        if '申报类型' in key:
            transaction_mode = key[:4]
            for rule_id in rule_keys:
                rule = rules[rule_id]
                for c in rule['constraints']:
                    if c['value'] == transaction_mode:
                        rule['constraints'].append({"key":"申报类型","operation":"is","value":preliminaries[key][0]})
                        vars[rule_id]['申报类型'] = []
                        break
    
    # 添加申报要素
    for key in prelim_keys:
        if '申报要素' in key:
            declaration_type = key[:4]
            for rule_id in rule_keys:
                rule = rules[rule_id]
                for c in rule['constraints']:
                    if declaration_type in c['value']:
                        elements = preliminaries[key]
                        element_str = "、".join(elements)
                        rule['constraints'].append({"key":"申报要素","operation":"is","value":element_str})
                        vars[rule_id]["申报要素"] = []
                        break
    


    return vars, rules





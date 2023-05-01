import json
import pprint
import copy


def compose_rules_r2_r3(defines, vars, rules, preliminaries, rule_name = 'rule'):
    """
    r2到r3的转换
    1. 结合状态机
    2. 添加一些预定义的要素
    """

    # 结合状态机
    vars, rules = compose_state_machine(vars, rules, preliminaries)
    # 添加一些预定义的要素
    vars, rules = add_elements(vars, rules, preliminaries)

    # 打印中间结果
    # with open(f"rules/r3_{rule_name}.txt", "w", encoding="utf-8") as f:
    #     f.write(pprint.pformat(rules))
    # print(f"R3包含的规则数：{len(rules.keys())}")

    return defines, vars, rules









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





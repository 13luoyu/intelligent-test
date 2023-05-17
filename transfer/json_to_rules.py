import json
import pprint

def get_rc(s):
    results, constraints, vs = [], [], []
    itc = [si.strip() for si in s.split("\n")]
    for si in itc:
        if si == '':
            continue
        cs = [sj.strip() for sj in si.split("and")]
        if 'then' in si:
            for i, c in enumerate(cs):
                if c == '':
                    continue
                if i == 0:
                    idx = 1
                else:
                    idx = 0
                items = c.split(" ")
                result = {}
                result['key'] = items[idx]
                result['value'] = items[idx+2]
                result['value'] = result["value"][1:-1]
                if result['value'] == "成功":
                    result['else'] = "失败"
                elif result['value'] == "失败":
                    result['else'] = "成功"
                else:
                    result['else'] = "不" + result['value']
                results.append(result)
        else:
            for i, c in enumerate(cs):
                if c == '':
                    continue
                if i == 0:
                    idx = 1
                else:
                    idx = 0
                items = c.split(" ")
                constraint = {}
                constraint['key'] = items[idx]
                if constraint['key'] not in vs:
                    vs.append(constraint['key'])
                if items[idx+1] == "is" or items[idx+1] == "in":
                    constraint['operation'] = items[idx+1]
                    constraint['value'] = items[idx+2]
                    if isinstance(constraint['value'], str) and constraint['operation'] == 'is':
                        constraint['value'] = constraint['value'][1:-1]
                else:
                    constraint['operation'] = "compute"
                    constraint['value'] = items[idx+1:]
                constraints.append(constraint)
    return results, constraints, vs


def json_to_r1(s):
    # d = json.loads(s)
    d = s
    rules_0 = d["rules"]
    preliminaries = d["领域知识"]
    defines, vars, rules = {}, {}, {}
    for rule in rules_0:
        rule_id = rule['subrule'] if 'subrule' in rule else rule['rule']
        rule_class = [rule['rule']] if isinstance(rule['rule'], str) else []
        focus = [rule['focus']]
        results, constraints, vs = get_rc(rule['context'])
        if len(results) != 0:
            rules[rule_id] = {"constraints":constraints,"results":results,"focus":focus,"rule_class":rule_class}
        else:
            rules[rule_id] = {"constraints":constraints,"focus":focus,"rule_class":rule_class}
        vars[rule_id] = {}
        for v in vs:
            vars[rule_id][v] = []
    # 额外的
    defines['交易市场'] = ["深圳证券交易所"]
    defines['交易品种'] = ["债券"]
    
    return defines, vars, rules, preliminaries



def json_to_r2(s):
    # d = json.loads(s)
    d = s
    rules_0 = d["rules"]
    preliminaries = d["领域知识"]
    defines, vars, rules = {}, {}, {}
    for rule in rules_0:
        rule_id = rule['rule']
        rule_class = rule['parent'] if 'parent' in rule else []
        focus = rule['focus']
        results, constraints, vs = get_rc(rule['context'])
        rules[rule_id] = {"constraints":constraints,"results":results,"focus":focus,"rule_class":rule_class}
        vars[rule_id] = {}
        for v in vs:
            vars[rule_id][v] = []
    # 额外的
    defines['交易市场'] = ["深圳证券交易所"]
    defines['交易品种'] = ["债券"]

    return defines, vars, rules, preliminaries


def json_to_r3(s):
    # d = json.loads(s)
    d = s
    rules_0 = d["rules"]
    defines, vars, rules = {}, {}, {}
    for rule in rules_0:
        rule_id = rule['rule']
        rule_class = rule['parent'] if 'parent' in rule else []
        focus = rule['focus']
        dependencies = rule['dependencies'] if 'dependencies' in rule else []
        results, constraints, vs = get_rc(rule['context'])
        rules[rule_id] = {"constraints":constraints,"results":results,"focus":focus,"rule_class":rule_class,"dependencies":dependencies}
        vars[rule_id] = {}
        for v in vs:
            vars[rule_id][v] = []
    # 额外的
    defines['交易市场'] = ["深圳证券交易所"]
    defines['交易品种'] = ["债券"]
    defines['前收盘价'] = ["100000"]
    defines['匹配成交最近成交价'] = ["100000"]
    defines['持仓面额'] = ["100000"]
    
    return defines, vars, rules




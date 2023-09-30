import json
import pprint

# 本文件的作用是，将内部数据格式rules写成json格式的R

def r2_to_json(rules):
    json_xtext = {}
    json_rules = []
    for rule_id in list(rules.keys()):
        rule = rules[rule_id]
        json_rule = {}
        json_rule['rule'] = rule_id
        json_rule['focus'] = rule['focus']

        xtext_str = "if "
        for c in rule['constraints']:
            if c['operation'] == 'is':
                xtext_str += f"{c['key']} {c['operation']} '{c['value']}' and "
            elif c['operation'] == 'in':
                xtext_str += f"{c['key']} {c['operation']} {c['value']} and "
        xtext_str = xtext_str[:-5]
        if 'results' in rule and len(rule['results']) > 0:
            xtext_str += ' \n then '
            for r in rule['results']:
                xtext_str += f"{r['key']} = '{r['value']}' and "
            xtext_str = xtext_str[:-4]
        has_constraint = False
        for c in rule['constraints']:
            if c['operation'] == 'compute':
                if not has_constraint:
                    xtext_str += ' \n constraint '
                    has_constraint = True
                else:
                    xtext_str += 'and '
                xtext_str += f"{c['key']} "
                for element in c['value']:
                    xtext_str += f"{element} "
        json_rule['context'] = xtext_str[:-1]

        json_rule['parent'] = rule['rule_class']
        json_rules.append(json_rule)
    json_xtext['rules'] = json_rules
    # json_xtext = json.dumps(json_xtext, ensure_ascii=False, indent=4)
    return json_xtext





def r3_to_json(rules):
    json_xtext = {}
    json_rules = []
    keys = list(rules.keys())
    for rule_id in keys:
        rule = rules[rule_id]
        json_rule = {}
        json_rule['rule'] = rule_id
        json_rule['focus'] = rule['focus']

        xtext_str = "if "
        for c in rule['constraints']:
            if c['operation'] == 'is':
                xtext_str += f"{c['key']} {c['operation']} '{c['value']}' and "
            elif c['operation'] == 'in':
                xtext_str += f"{c['key']} {c['operation']} {c['value']} and "
        xtext_str = xtext_str[:-5]
        if 'results' in rule and len(rule['results']) > 0:
            xtext_str += ' \n then '
            for r in rule['results']:
                xtext_str += f"{r['key']} = '{r['value']}' and "
            xtext_str = xtext_str[:-4]
        has_constraint = False
        for c in rule['constraints']:
            if c['operation'] == 'compute':
                if not has_constraint:
                    xtext_str += ' \n constraint '
                    has_constraint = True
                else:
                    xtext_str += 'and '
                xtext_str += f"{c['key']} "
                for element in c['value']:
                    xtext_str += f"{element} "
        json_rule['context'] = xtext_str[:-1]

        json_rule['parent'] = rule['rule_class']
        
        dependencies = []
        # 如果一个规则a的constraints中的订单状态=另一个规则b的results中的订单状态，那么这个规则a的dependencies就是b
        order_state = ""
        for c in rule['constraints']:
            if c['key'] == "订单状态":
                order_state = c['value']
                break
        if order_state != "":
            for id1 in keys:
                if id1 == rule_id:
                    continue
                rule1 = rules[id1]
                order_state1 = ""
                if 'results' not in rule1:
                    continue
                for r in rule1['results']:
                    if r['key'] == "订单状态":
                        order_state1 = r['value']
                        break
                if order_state == order_state1:
                    dependencies.append(id1)

        json_rule['dependencies'] = dependencies

        json_rules.append(json_rule)
    json_xtext['rules'] = json_rules
    # json_xtext = json.dumps(json_xtext, ensure_ascii=False, indent=4)
    return json_xtext

def to_mydsl(json_text):
    rules = json_text["rules"]
    s = ""
    for rule in rules:
        s += f"rule {rule['rule']}\n"
        s += f"focus: {','.join(rule['focus'])}\n"
        rule['context'] = rule['context'].replace("\n ", "\n\t")
        s += f"\t{rule['context']}\n\n"
    return s

if __name__ == "__main__":
    r2_rules = json.load(open("../ours/rules_cache/r2.json", "r", encoding="utf-8"))
    r2_json = r2_to_json(r2_rules)
    r2 = to_mydsl(r2_json)
    with open("../ours/rules_cache/r2.mydsl", "w", encoding="utf-8") as f:
        f.write(r2)
    r3_rules = json.load(open("../ours/rules_cache/r3.json", "r", encoding="utf-8"))
    r3_json = r3_to_json(r3_rules)
    r3 = to_mydsl(r3_json)
    with open("../ours/rules_cache/r3.mydsl", "w", encoding="utf-8") as f:
        f.write(r3)
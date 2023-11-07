import json
import pprint
import cn2an

# 本文件的作用是，将内部数据格式rules写成json格式的R

def r2_to_json(rules):
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
            xtext_str += '\nthen '
            for r in rule['results']:
                xtext_str += f"{r['key']} is '{r['value']}' and "
            xtext_str = xtext_str[:-4]
        has_constraint = False
        for c in rule['constraints']:
            if c['operation'] == 'compute':
                if not has_constraint:
                    xtext_str += '\nconstraint '
                    has_constraint = True
                else:
                    xtext_str += 'and '
                xtext_str += f"{c['key']} "
                for element in c['value']:
                    xtext_str += f"{element} "
        json_rule['context'] = xtext_str[:-1]

        json_rule['parent'] = rule['rule_class']
        json_rules.append(json_rule)
    return json_rules





def r3_to_json(rules):
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
            xtext_str += '\nthen '
            for r in rule['results']:
                xtext_str += f"{r['key']} = '{r['value']}' and "
            xtext_str = xtext_str[:-4]
        has_constraint = False
        for c in rule['constraints']:
            if c['operation'] == 'compute':
                if not has_constraint:
                    xtext_str += '\nconstraint '
                    has_constraint = True
                else:
                    xtext_str += 'and '
                xtext_str += f"{c['key']} "
                for element in c['value']:
                    xtext_str += f"{element} "
        json_rule['context'] = xtext_str[:-1]

        json_rule['parent'] = rule['rule_class']
        
        json_rule['before'] = rule['before']
        json_rule['after'] = rule['after']

        json_rules.append(json_rule)
    return json_rules

def to_mydsl(json_rules):
    if len(json_rules) == 0:
        return ""
    if "第" in json_rules[0]['rule'] and "条" in json_rules[0]['rule']:
        for rule in json_rules:
            rule['temp_id'] = cn2an.cn2an(rule['rule'].split(".")[0][1:-1], 'normal')
        rules = sorted(json_rules, key=lambda x:x['temp_id'])
    else:
        rules = sorted(json_rules, key=lambda x:x['rule'])
    s = ""
    for rule in rules:
        s += f"rule {rule['rule']}\n"
        s += f"sourceId {','.join(rule['parent'])}\n"
        s += f"focus: {','.join(rule['focus'])}\n"
        if 'before' in rule:
            s += f"before: {rule['before']}\n"
        if 'after' in rule:
            s += f"after: {rule['after']}\n"
        rule['context'] = rule['context'].replace("\n", "\n\t")
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
from transfer.mydsl_to_rules import mydsl_to_rules_v2
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

def rules_to_mydsl(json_rules):
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





def rules_to_mydsl_v2(rules):
    s = ""
    for rule_id in list(rules.keys()):
        rule = rules[rule_id]
        s += f"rule {rule_id}\n"
        s += f"sourceId {','.join(rule['rule_class'])}\n"
        s += f"focus: {','.join(rule['focus'])}\n"
        if "before" in rule:
            s += f"before: {rule['before']}\n"
        if "after" in rule:
            s += f"after: {rule['after']}\n"
        s += "\tif "
        for c in rule['constraints']:
            if c['operation'] == "is":
                s += f"{c['key']} is \"{c['value']}\" and "
            elif c['operation'] == "in":
                s += f"{c['key']} in {c['value']} and "
            elif c['operation'] == "compute":
                s += f"{c['key']} "
                for element in c['value']:
                    s += f"{element} "
                s += "and "
            else:
                raise ValueError(f"未定义的规则操作符: {c['operation']} !")
        s = s[:-5] + "\n\tthen "
        for c in rule['results']:
            if c['operation'] == "is":
                s += f"{c['key']} is \"{c['value']}\" and "
            elif c['operation'] == "in":
                s += f"{c['key']} in {c['value']} and "
            elif c['operation'] == "compute":
                s += f"{c['key']} "
                for element in c['value']:
                    s += f"{element} "
                s += "and "
            else:
                raise ValueError(f"未定义的规则操作符: {c['operation']} !")
        s = s[:-5] + "\n\n"
    return s




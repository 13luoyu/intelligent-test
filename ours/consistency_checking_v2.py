from transfer.mydsl_to_rules import mydsl_to_rules_v2
import z3
import copy
import pprint

# 使用一个标识标记 "可以"、"必须"，标识在组装时实现，可以为canbe，必须为is
# 将 "key canbe value" 改为 "key is value or key isn't value"
# 或关系规则判断是否冲突，1、单规则之间比较，不考虑or；2、单规则和一组or规则比较，如果或关系存在于if，分成多个规则照常判断；如果存在于then，冲突；3、两组or规则比较，如果或关系存在于if，分成多个规则并照常判断；如果或关系存在于then，要求比较的两组规则必须一一对应才不冲突



def transfer_canbe_to_is(rules):

    new_rules = {}
    keys = sorted(list(rules.keys()))
    next_orId = 0
    for rule_id in keys:
        if "orId" in rules[rule_id]:
            next_orId = max(next_orId, rules[rule_id]['orId'])
    next_orId += 1
    for rule_id in keys:
        rule = rules[rule_id]
        rule['rule'] = rule_id
        new_rule = None
        for result in rule['results']:
            if result['operation'] == "canbe":
                if new_rule is None:
                    new_rule = copy.deepcopy(rule)
                result['operation'] = "is"
        if new_rule is not None:
            for result in new_rule['results']:
                if result['operation'] == "canbe":
                    result['operation'] = "is"
                    result['value'] = "not" + result['value']
            if "orId" not in new_rule:
                new_rule['orId'] = next_orId
                rule['orId'] = next_orId
                next_orId += 1
            
            new_id = rule_id + "#2"
            new_rule['rule'] = new_id
            new_rules[new_id] = new_rule
            rule['rule'] = rule_id + "#1"
            new_rules[rule_id + "#1"] = rule
        else:
            new_rules[rule_id] = rule

    # pprint.pprint(new_rules)
    return new_rules


def check_single_rule(rulei_if_keys, rulei_if_values, rulei_then_keys, rulei_then_values, rulej_if_keys, rulej_if_values, rulej_then_keys, rulej_then_values):

    s = z3.Solver()
    variables = {}

    # if情况0
    for index, key in enumerate(rulei_if_keys):
        if key not in variables:
            v = z3.String(key)
            variables[key] = v
        else:
            v = variables[key]
        s.push()
        s.add(v == rulei_if_values[index])
    for index, key in enumerate(rulej_if_keys):
        if key not in variables:
            v = z3.String(key)
            variables[key] = v
        else:
            v = variables[key]
        s.push()
        s.add(v == rulej_if_values[index])
    if s.check() == z3.unsat:
        # 规则 i, j 的条件部分，存在相同条件具有不同值的情况，不冲突
        return False
    
    # 情况1、2、3、4
    s.reset()
    # s.check(~(R1.if ∩ ~R2.if)) == UNSAT
    consi = ""
    for index, key in enumerate(rulei_if_keys):
        if key not in variables:
            v = z3.String(key)
            variables[key] = v
        else:
            v = variables[key]
        if isinstance(consi, str):
            consi = v == rulei_if_values[index]
        else:
            consi = z3.And(consi, v == rulei_if_values[index])
    consj = ""
    for index, key in enumerate(rulej_if_keys):
        if key not in variables:
            v = z3.String(key)
            variables[key] = v
        else:
            v = variables[key]
        if isinstance(consj, str):
            consj = v == rulej_if_values[index]
        else:
            consj = z3.And(consj, v == rulej_if_values[index])
    s.add(z3.And(consi, z3.Not(consj)))
    # s.add(z3.Not(z3.Implies(consi, consj)))
    if s.check() == z3.unsat:  # if情况1、2，继续判断then
        s.reset()
        consi = []
        for index, key in enumerate(rulei_then_keys):
            if key not in variables:
                v = z3.String(key)
                variables[key] = v
            else:
                v = variables[key]
            if "not" in rulei_then_values[index]:
                consi.append(v != rulei_then_values[index].split("not")[-1])
            else:
                consi.append(v == rulei_then_values[index])
        consj = []
        for index, key in enumerate(rulej_then_keys):
            if key not in variables:
                v = z3.String(key)
                variables[key] = v
            else:
                v = variables[key]
            if "not" in rulej_then_values[index]:
                consj.append(v != rulej_then_values[index].split("not")[-1])
            else:
                consj.append(v == rulej_then_values[index])
        for con in consi + consj:
            s.push()
            s.add(con)
        # 两个以上不冲突，假设：时间、数量这样的不会同时出现在then中
        if s.check() == z3.unsat:
            keys = list(set(rulei_then_keys + rulej_then_keys))
            for ignore_key in keys:
                s.reset()
                for index, key in enumerate(rulei_then_keys):
                    if key != ignore_key:
                        s.push()
                        s.add(consi[index])
                for index, key in enumerate(rulej_then_keys):
                    if key != ignore_key:
                        s.push()
                        s.add(consj[index])
                if s.check() == z3.sat:
                    # 规则 i,j 的条件部分相同，结论部分只有一个互相冲突的变量，冲突")
                    return True
            # 规则 i, j 的条件部分相同，结论部分存在两个或以上互相冲突的变量，不冲突
            return False
        else:
            # 规则 i, j 的条件部分相同，结论部分可以并存，不冲突
            return False

    else:  # if情况3、4
        # 规则 i, j 的条件部分，互相存在对方没有的条件，不冲突
        return False



def check_single_rule_and_ruleset(ruleset, single_rule):
    record = []
    for rule in ruleset:
        conflict = check_single_rule(single_rule[1], single_rule[2], single_rule[3], single_rule[4], rule[1], rule[2], rule[3], rule[4])
        record.append(conflict)
    if any(record):
        return True, record
    return False, record



def check_ruleset(ruleset1, ruleset2):
    records = [True] * len(ruleset2)
    for rule1 in ruleset1:
        conflict, record = check_single_rule_and_ruleset(ruleset2, rule1)
        # if not conflict:
        #     return False
        records = [r1 & r2 for (r1, r2) in zip(records, record)]
    if any(records):
        return True
    
    records = [True] * len(ruleset1)
    for rule2 in ruleset2:
        conflict, record = check_single_rule_and_ruleset(ruleset1, rule2)
        # if not conflict:
        #     return False
        records = [r1 & r2 for (r1, r2) in zip(records, record)]
    if any(records):
        return True

    return False








def consistency_checking_v2(rules):

    rules = transfer_canbe_to_is(rules)

    rule_if_keys, rule_if_values = [], []
    rule_then_keys, rule_then_values = [], []
    no_relation_rules, or_relation_rules = [], []
    or_relation_map = {}

    # no_relation_rules = [
    #   (rule_id, rule_if_keys[i], rule_if_values[i], rule_then_keys[i], rule_then_values[i]),  //一条规则
    #   ...
    # ]

    # no_relation_rules = [
    #   [
    #      (rule_id, rule_if_keys[i], rule_if_values[i], rule_then_keys[i], rule_then_values[i]),
    #      ...
    #   ],  //一组具有or关系的规则
    #   [], ...
    # ]

    for rule_id in list(rules.keys()):
        keys, values = [], []
        for c in rules[rule_id]['constraints']:
            keys.append(c['key'])
            values.append(c['value'])
        rule_if_keys.append(keys)
        rule_if_values.append(values)
        keys, values = [], []
        for c in rules[rule_id]['results']:
            keys.append(c['key'])
            values.append(c['value'])
        rule_then_keys.append(keys)
        rule_then_values.append(values)

        if "orId" in rules[rule_id]:
            if rules[rule_id]["orId"] in or_relation_map:
                or_relation_map[rules[rule_id]["orId"]].append((rule_id, rule_if_keys[-1], rule_if_values[-1], rule_then_keys[-1], rule_then_values[-1]))
            else:
                or_relation_map[rules[rule_id]["orId"]] = [(rule_id, rule_if_keys[-1], rule_if_values[-1], rule_then_keys[-1], rule_then_values[-1])]
        else:
            no_relation_rules.append((rule_id, rule_if_keys[-1], rule_if_values[-1], rule_then_keys[-1], rule_then_values[-1]))
    
    or_relation_rules = list(or_relation_map.values())
    # pprint.pprint(or_relation_rules)

    
    for i in range(len(no_relation_rules)):
        for j in range(len(no_relation_rules)):
            if i >= j:
                continue
            conflict = check_single_rule(no_relation_rules[i][1], no_relation_rules[i][2], no_relation_rules[i][3], no_relation_rules[i][4], no_relation_rules[j][1], no_relation_rules[j][2], no_relation_rules[j][3], no_relation_rules[j][4])
            if conflict:
                print(f"规则 {no_relation_rules[i][0]} 和 {no_relation_rules[j][0]} 冲突")
    

    for i in range(len(or_relation_rules)):
        for j in range(len(no_relation_rules)):
            conflict, _ = check_single_rule_and_ruleset(or_relation_rules[i], no_relation_rules[j])
            if conflict:
                print(f"规则 {no_relation_rules[j][0]} 和规则集 {','.join([r[0] for r in or_relation_rules[i]])} 冲突")


    for i in range(len(or_relation_rules)):
        for j in range(len(or_relation_rules)):
            if i >= j:
                continue
            conflict = check_ruleset(or_relation_rules[i], or_relation_rules[j])
            if conflict:
                print(f"规则集 {','.join([r[0] for r in or_relation_rules[i]])} 和规则集 {','.join([r[0] for r in or_relation_rules[j]])} 冲突")





if __name__ == "__main__":
    file = "rules_cache/consistency_checking_input_v2.mydsl"
    s = open(file, "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules_v2(s)
    consistency_checking_v2(rules)
from transfer.mydsl_to_rules import mydsl_to_rules_v2
import z3

# 0: if s.check(R1.if ∩ R2.if) == UNSAT  不冲突  if存在key相同，value不同的情况

# s.check(~(R1.if ∩ ~R2.if)) == UNSAT and (R1.then == R2.then)
# 1: if 相同      R1.if ∩ R2.if == R1.if == R2.if  继续判断then  
# 2: if 包含关系  R1.if ∩ R2.if == R1.if || R1.if ∩ R2.if == R2.if  继续判断then

# then如果为相同或包含关系，判断相交部分
# then如果为交集或无交集，不冲突

# 3: if 交集      R1.if ∩ R2.if != 空  不冲突
# 4: if 无交集    R1.if ∩ R2.if == 空  不冲突



def consistency_checking_v2(rules):
    rule_if_keys, rule_if_values = [], []
    rule_then_keys, rule_then_values = [], []
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
    
    for i in range(len(rules)):
        for j in range(len(rules)):
            if j <= i:
                continue
            rulei_keys, rulei_values = rule_if_keys[i], rule_if_values[i]
            rulej_keys, rulej_values = rule_if_keys[j], rule_if_values[j]

            s = z3.Solver()
            variables = {}

            # if情况0
            for index, key in enumerate(rulei_keys):
                if key not in variables:
                    v = z3.String(key)
                    variables[key] = v
                else:
                    v = variables[key]
                s.push()
                s.add(v == rulei_values[index])
            for index, key in enumerate(rulej_keys):
                if key not in variables:
                    v = z3.String(key)
                    variables[key] = v
                else:
                    v = variables[key]
                s.push()
                s.add(v == rulej_values[index])
            if s.check() == z3.unsat:
                # print(f"规则 {list(rules.keys())[i]}, {list(rules.keys())[j]} 的条件部分，存在相同条件具有不同值的情况，不冲突")
                continue
            
            # 情况1、2、3、4
            s.reset()
            # s.check(~(R1.if ∩ ~R2.if)) == UNSAT
            consi = ""
            for index, key in enumerate(rulei_keys):
                if key not in variables:
                    v = z3.String(key)
                    variables[key] = v
                else:
                    v = variables[key]
                if isinstance(consi, str):
                    consi = v == rulei_values[index]
                else:
                    consi = z3.And(consi, v == rulei_values[index])
            consj = ""
            for index, key in enumerate(rulej_keys):
                if key not in variables:
                    v = z3.String(key)
                    variables[key] = v
                else:
                    v = variables[key]
                if isinstance(consj, str):
                    consj = v == rulei_values[index]
                else:
                    consj = z3.And(consj, v == rulei_values[index])
            s.add(z3.And(consi, z3.Not(consj)))
            # s.add(z3.Not(z3.Implies(consi, consj)))
            if s.check() == z3.unsat:  # if情况1、2
                s.reset()
                rulei_keys, rulei_values = rule_then_keys[i], rule_then_values[i]
                rulej_keys, rulej_values = rule_then_keys[j], rule_then_values[j]
                consi = ""
                for index, key in enumerate(rulei_keys):
                    if key not in variables:
                        v = z3.String(key)
                        variables[key] = v
                    else:
                        v = variables[key]
                    if isinstance(consi, str):
                        consi = v == rulei_values[index]
                    else:
                        consi = z3.And(consi, v == rulei_values[index])
                consj = ""
                for index, key in enumerate(rulej_keys):
                    if key not in variables:
                        v = z3.String(key)
                        variables[key] = v
                    else:
                        v = variables[key]
                    if isinstance(consj, str):
                        consj = v == rulej_values[index]
                    else:
                        consj = z3.And(consj, v == rulej_values[index])
                
                s.add(z3.And(consi, consj))
                if s.check() == z3.unsat:
                    print(f"规则 {list(rules.keys())[i]}, {list(rules.keys())[j]} 的条件部分相同，结论部分存在互相冲突的部分，冲突")
                    continue
                
                # s.reset()
                # s.add(z3.And(consi, z3.Not(consj)))
                # # s.add(z3.Not(z3.Implies(consi, consj)))
                # if s.check() == z3.unsat:  # then情况1、2
                #     print(f"规则 {list(rules.keys())[i]}, {list(rules.keys())[j]} 的条件部分相同，结论部分存在互相冲突的部分，冲突")
                # else:  # if情况3、4
                #     print(f"规则 {list(rules.keys())[i]}, {list(rules.keys())[j]} 的条件部分相同，结论部分存在对方没有的条件，不冲突")

            else:  # if情况3、4
                print(f"规则 {list(rules.keys())[i]}, {list(rules.keys())[j]} 的条件部分，互相存在对方没有的条件，不冲突")








if __name__ == "__main__":
    file = "rules_cache/consistency_checking_input_v2.mydsl"
    s = open(file, "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules_v2(s)
    consistency_checking_v2(rules)
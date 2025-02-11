from transfer.mydsl_to_rules import mydsl_to_rules
import z3
import copy
import pprint

# 使用一个标识标记 "可以"、"必须"，标识在组装时实现，可以为canbe，必须为is
# 将 "key canbe value" 改为 "key is value or key is notvalue"
# 或关系规则判断是否冲突，1、单规则之间比较，不考虑or；2、单规则和一组or规则比较，如果或关系存在于if，分成多个规则照常判断；如果存在于then，冲突；3、两组or规则比较，如果或关系存在于if，分成多个规则并照常判断；如果或关系存在于then，要求比较的两组规则必须一一对应才不冲突



def transfer_canbe_to_is(rules):
    """
    将类似操作、操作部分的key对应的operation改为canbe。后面可能需要完善 TODO
    如果一个规则中存在 "key canbe value"，则将其转换为 "key is value" or "key is notvalue"的两条规则，并且使用orId进行关联
    """
    canbe_key = ["操作", "操作部分"]
    keys = sorted(list(rules.keys()))
    for rule_id in keys:
        rule = rules[rule_id]
        for r in rule['results']:
            if r['key'] in canbe_key:
                r['operation'] = "canbe"

    new_rules = {}
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

    return new_rules


def get_cons(rule_then_keys, rule_then_values, ignore_keys=[], variables = {}):
    """
    将规则的then部分生成SMT表达式。主要考虑两种情况：1、一个key有一个value，生成一个表达式；2、一个key有多个value，这些value间以or关系关联，生成一个表达式。返回所有key-value(s)表达式数组
    """
    cons = []  # key-value(s)表达式数组
    cache = []  # 缓存多个value的情况
    cache_empty=True
    for index, key in enumerate(rule_then_keys):
        if key in ignore_keys:
            continue
        if key not in variables:
            v = z3.String(key)
            variables[key] = v
        else:
            v = variables[key]
        if "," not in rule_then_values[index]:
            if "not" in rule_then_values[index]:
                cons.append(v != rule_then_values[index].split("not")[-1])
            else:
                cons.append(v == rule_then_values[index])
        else:
            for idx, val in enumerate(rule_then_values[index].split(",")):
                if cache_empty:
                    c = []
                    c.append(v == val)
                    cache.append(c)
                else:
                    cache[idx].append(v == val)
            cache_empty=False
    if cache != []:
        y = ""
        for c in cache:
            x = ""
            for constraint in c:
                if isinstance(x, str):
                    x = constraint
                else:
                    x = z3.And(x, constraint)
            if isinstance(y, str):
                y = x
            else:
                y = z3.Or(y, x)
        cons.append(y)
    return cons

def get_z3_expression(cons):
    """
    将cons数组以and相连组装成z3表达式
    """
    if len(cons) > 1:
        x = ""
        for con in cons:
            if isinstance(x, str):
                x = con
            else:
                x = z3.And(x, con)
        z3_exp = x
    else:
        z3_exp = cons[0]
    return z3_exp



def check_rule_pair(rule1, rule2):
    """
    检查并返回rule1和rule2是否冲突
    """
    s = z3.Solver()
    variables = {}

    # 首先提取if, then中的key和value，并对then中的or情况进行处理，写在一起
    if isinstance(rule1, tuple):
        rulei_if_keys, rulei_if_values, rulei_then_keys, rulei_then_values = rule1[1:]
    else:
        rulei_if_keys, rulei_if_values, rulei_then_keys, rulei_then_values = rule1[0][1:]
        for rule in rule1[1:]:
            # 默认if中不存在or关系，将then中的or关系进行组装，组装方法是以逗号分隔写在一个字符串中
            for i in range(len(rule[3])):
                if rule[3][i] not in rulei_then_keys:
                    rulei_then_keys.append(rule[3][i])
                    rulei_then_values.append(rule[4][i])
                else:
                    p = rulei_then_keys.index(rule[3][i])
                    rulei_then_values[p] = rulei_then_values[p] + "," + rule[4][i]
    
    if isinstance(rule2, tuple):
        rulej_if_keys, rulej_if_values, rulej_then_keys, rulej_then_values = rule2[1:]
    else:
        rulej_if_keys, rulej_if_values, rulej_then_keys, rulej_then_values = rule2[0][1:]
        for rule in rule2[1:]:
            for i in range(len(rule[3])):
                if rule[3][i] not in rulej_then_keys:
                    rulej_then_keys.append(rule[3][i])
                    rulej_then_values.append(rule[4][i])
                else:
                    p = rulej_then_keys.index(rule[3][i])
                    rulej_then_values[p] = rulej_then_values[p] + "," + rule[4][i]

    # Example: 
    # rulei_if_keys = ['时间']
    # rulei_if_values = ['竞买日前']
    # rulei_then_keys = ['数量']
    # rulei_then_values = ['10万元面额或者其整数倍']
    # rulej_if_keys = ['时间']
    # rulej_if_values = ['竞买日前']
    # rulej_then_keys = ['操作主体', '操作', '操作部分']
    # rulej_then_values = ['卖方,卖方,卖方,卖方', '修改,撤销,not修改,not撤销', '竞买预约要素,竞买,not竞买预约要素,not竞买']


    # 判断规则的if部分是否存在相同key的value不同，方法是将if部分所有key-value以and关联放入求解器，如果unsat则if部分存在相同key的value不同
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
        # 规则 i, j 的条件部分，存在相同key具有不同value的情况，规则不冲突
        return False


    # 现在if部分要么没有共同的key，要么相同的key具有相同的value，需要判别这两种情况
    # 方法是将一个规则所有约束取反，并和另一个规则以and相连
    # 如果它们具有相同的key，并且相同的key有相同的value，那么求解器结果为unsat
    # s.check(~(R1.if ∩ ~R2.if)) == UNSAT
    s.reset()
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
    # 上式等价于：s.add(z3.Not(z3.Implies(consi, consj)))

    if s.check() == z3.sat:
        s.reset()
        s.add(z3.And(consj, z3.Not(consi)))
    
    if s.check() == z3.unsat:  # 规则i,j的if部分有交集，且交集key对应value完全相同
        s.reset()
        # 现在两个规则的if部分可以相容，判断then部分
        # 1、如果then部分没有共同的key则不冲突，否则进行后续判断
        # 2、有共同的key分为三种情况：有交集、包含、相同
        # 如果key为交集、包含，则冲突
        # 如果key相同，value有且仅有一个不同，则冲突；value完全相同，或有两个以上不同，则不冲突
        # 3、取交集的方法是在构建z3表达式时，如果key不在交集中，则不将其考虑在z3表达式中
        # 4、判断交集key对应value是否完全相同的方法是，若
        # 任意x p(x)->q(x) and q(x)->p(x) == sat 
        # 则交集key对应value完全相同，将表达式"左右取反"可以输入z3求解。（两边取反：存在x 非(p(x)->q(x)) or 非(q(x)->p(x)) == unsat）
        # 否则，存在一至多个冲突
        # 5、判断是否存在多个冲突的方法是，随机去掉其中一个key及其对应value，剩下的输入到求解器中判断是否冲突
        # 如果存在一个key-value被去掉后求解器sat，说明仅有这一个key-value冲突
        # 如果所有key遍历完成后都是unsat，则说明有两个以上的冲突

        intersection_keys = list(set(rulei_then_keys) & set(rulej_then_keys))
        if len(intersection_keys) == 0:
            # then部分没有key重叠，不冲突
            return False

        # rulei_ignore_keys = [key for key in rulei_then_keys if key not in intersection_keys]
        # rulej_ignore_keys = [key for key in rulej_then_keys if key not in intersection_keys]
        rulei_ignore_keys = []
        rulej_ignore_keys = []  # 这里ignore与否都是等价的，因为每个规则then部分独有的key-value不会影响冲突

        # 将then部分生成SMT表达式
        consi = get_cons(rulei_then_keys, rulei_then_values, ignore_keys=rulei_ignore_keys, variables=variables)
        consj = get_cons(rulej_then_keys, rulej_then_values, ignore_keys=rulej_ignore_keys, variables=variables)
        # print(consi)
        # print(consj)
        z3_expi = get_z3_expression(consi)
        z3_expj = get_z3_expression(consj)
        # print(z3_expi)
        # print(z3_expj)

        s.add(z3.Or(z3.Not(z3.Implies(z3_expi, z3_expj)), z3.Not(z3.Implies(z3_expj, z3_expi))))
        # 两个以上不冲突，假设：时间、数量这样的不会同时出现在then中
        if s.check() == z3.sat:  # 存在冲突
            keys = list(set(rulei_then_keys + rulej_then_keys))
            for ignore_key in keys:
                s.reset()
                consi = get_cons(rulei_then_keys, rulei_then_values, ignore_keys= rulei_ignore_keys + [ignore_key], variables=variables)
                consj = get_cons(rulej_then_keys, rulej_then_values, ignore_keys= rulej_ignore_keys + [ignore_key], variables=variables)
                if len(consi) == 0 or len(consj) == 0:
                    return True
                z3_expi = get_z3_expression(consi)
                z3_expj = get_z3_expression(consj)

                s.add(z3.Or(z3.Not(z3.Implies(z3_expi, z3_expj)), z3.Not(z3.Implies(z3_expj, z3_expi))))
                if s.check() == z3.unsat:  # 存在不冲突情况
                    # 规则 i,j 的条件部分有交集，结论部分只有一个互相冲突的变量，冲突")
                    return True
            # 规则 i, j 的条件部分有交集，结论部分存在两个或以上互相冲突的变量，不冲突
            return False
        else:
            # 规则 i, j 的条件部分有交集，结论部分可以并存，不冲突
            return False

    else:  # 规则 i, j 的条件部分不存在交集，不冲突
        return False





def consistency_checking(rules):
    """
    rules = {
        "rule_id": {
            "rule_class": ['1'],
            "orId": 2  # 可选
            "focus": ["时间"],
            "constraints": [
                {"key":"时间", "operation":"is", "value":"竞买日前"},
                ...
            ],
            "results": [
                {"key":"数量", "operation":"is", "value":"10万元面额或者其整数倍"},
                ...
            ]
        }
    }
    """
    conflict_rules = []
    # rules = transfer_canbe_to_is(rules)

    rule_if_keys, rule_if_values = [], []
    rule_then_keys, rule_then_values = [], []
    no_relation_rules, or_relation_rules = [], []
    or_relation_map = {}

    # no_relation_rules = [
    #   (rule_id, rule_if_keys[i], rule_if_values[i], rule_then_keys[i], rule_then_values[i]),  //一条规则
    #   ...
    # ]

    # or_relation_rules = [
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
            if c['operation'] == "is":
                values.append(c['value'])
            else:
                values.append(c['operation'] + c['value'])
        rule_if_keys.append(keys)
        rule_if_values.append(values)
        keys, values = [], []
        for c in rules[rule_id]['results']:
            keys.append(c['key'])
            if c['operation'] == "is":
                values.append(c['value'])
            else:
                values.append(c['operation'] + c['value'])
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

    # check consistency
    all_rules = no_relation_rules + or_relation_rules
    for i in range(len(all_rules)):
        for j in range(len(all_rules)):
            if i >= j:
                continue
            conflict = check_rule_pair(all_rules[i], all_rules[j])
            if conflict:
                rule_id1 = all_rules[i][0].split("#")[0] if isinstance(all_rules[i][0], str) else ",".join(list(set([idi[0].split("#")[0] for idi in all_rules[i]])))
                rule_id2 = all_rules[j][0].split("#")[0] if isinstance(all_rules[j][0], str) else ",".join(list(set([idi[0].split("#")[0] for idi in all_rules[j]])))
                print(f"规则 {rule_id1} 和 {rule_id2} 冲突")
                conflict_rules.append([rule_id1, rule_id2])
    
    return conflict_rules






if __name__ == "__main__":
    file = "cache/consistency_checking_input.mydsl"
    s = open(file, "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules(s)
    consistency_checking(rules)






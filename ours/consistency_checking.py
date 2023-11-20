import json
import pprint
from transfer.mydsl_to_rules import mydsl_to_rules
import copy

def consistency_checking(data):
    defines, vars, rules = mydsl_to_rules(data)
    conflict_rules = []  # {ids: [id1, id2], reason: ''}
    general_keys = ['交易市场', '交易方式', '交易品种', '交易方向', '事件', '状态', '操作', '操作人', '操作部分']
    rule_ids = list(rules.keys())
    for i, id1 in enumerate(rule_ids):
        for j, id2 in enumerate(rule_ids):
            if j <= i:
                continue
            rule1, rule2 = rules[id1], rules[id2]
            cons1, cons2, res1, res2 = sorted(rule1['constraints'], key=lambda x:x['key']), sorted(rule2['constraints'], key=lambda x:x['key']), sorted(rule1['results'], key=lambda x:x['key']), sorted(rule2['results'], key=lambda x:x['key'])
            
            then_same = True
            if len(res1) != len(res2):
                then_same = False
            else:
                for ri, r1 in enumerate(res1):
                    r2 = res2[ri]
                    if r1 != r2:
                        then_same = False
                        break
            
            if_same = True
            if len(cons1) != len(cons2):
                if_same = False
            else:
                for ci, c1 in enumerate(cons1):
                    c2 = cons2[ci]
                    if c1 != c2:
                        if_same = False
                        break
            
            if then_same:
                if if_same:
                    continue
                else:
                    # 判断cons1的key和cons2的key之间的关系
                    cons1_keys, cons2_keys = [con['key'] for con in cons1], [con['key'] for con in cons2]
                    cons1_value, cons2_value = [con['value'] for con in cons1], [con['value'] for con in cons2]
                    # 统计两个规则中的每个key的数量
                    count1, count2 = {}, {}
                    for key in cons1_keys:
                        if key in count1:
                            count1[key] += 1
                        else:
                            count1[key] = 1
                    for key in cons2_keys:
                        if key in count2:
                            count2[key] += 1
                        else:
                            count2[key] = 1
                    cons1_in_cons2, cons2_in_cons1, interact = True, True, False
                    for key in list(count1.keys()):
                        if key in count2:
                            interact = True
                        elif key in count2 and count1[key] != count2[key] or key not in count2:
                            cons1_in_cons2 = False
                    for key in list(count2.keys()):
                        if key in count1 and count1[key] != count2[key] or key not in count1:
                            cons2_in_cons1 = False
                            break
                    
                    if cons1_in_cons2 and cons2_in_cons1:  # key相同
                        general_diff = False
                        other_diff_idx = []
                        for vi, v1 in enumerate(cons1_value):
                            v2 = cons2_value[vi]
                            if v1 != v2 and cons1_keys[vi] in general_keys:
                                general_diff = True
                                break
                            elif v1 != v2 and cons1_keys[vi] not in general_keys:
                                other_diff_idx.append(vi)
                        if general_diff:
                            # 不冲突
                            continue
                        else:
                            # 冲突
                            reason = f"规则{id1}和{id2}的结果相同，但存在互相冲突的约束：对规则{id1}，"
                            for idx in other_diff_idx:
                                reason += f"{cons1_keys[idx]}为{cons1_value[idx]}，"
                            reason += f"而对规则{id2}，"
                            for idx in other_diff_idx:
                                reason += f"{cons2_keys[idx]}为{cons2_value[idx]}，"
                            reason = f"{reason[:-1]}。"
                            conflict_rules.append({"rule_ids":[id1, id2], "reason":reason})
                    elif cons1_in_cons2 or cons2_in_cons1:
                        # 判断相交部分的value是否完全相同
                        interact_same = True
                        if cons1_in_cons2:
                            for ki, key1 in enumerate(cons1_keys):
                                kv_diff = True
                                for kj, key2 in enumerate(cons2_keys):
                                    if key1 == key2 and cons1_value[ki] == cons2_value[kj]:
                                        kv_diff = False
                                        break
                                if kv_diff:
                                    interact_same = False
                                    break
                            # 将cons2_keys和cons2_value设置为交集部分
                            interact_cons2_keys = copy.deepcopy(cons1_keys)
                            interact_cons2_value = []
                            for ki, key in enumerate(interact_cons2_keys):
                                v1 = cons1_keys[ki]
                                last = ""
                                for vi, v2 in enumerate(cons2_value):
                                    if key == cons2_keys[vi] and v1 == v2:
                                        interact_cons2_value.append(v1)
                                        last = ""
                                        break
                                    elif key == cons2_keys[vi] and v1 != v2:
                                        last = v2
                                if last != "":
                                    interact_cons2_value.append(last)
                            cons2_keys = interact_cons2_keys
                            cons2_value = interact_cons2_value
                        else:
                            for ki, key2 in enumerate(cons2_keys):
                                kv_diff = True
                                for kj, key1 in enumerate(cons1_keys):
                                    if key1 == key2 and cons1_value[kj] == cons2_value[ki]:
                                        kv_diff = False
                                        break
                                if kv_diff:
                                    interact_same = False
                                    break
                            # 将cons1_keys和cons1_value设置为交集部分
                            interact_cons1_keys = copy.deepcopy(cons2_keys)
                            interact_cons1_value = []
                            for ki, key in enumerate(interact_cons1_keys):
                                v2 = cons2_keys[ki]
                                last = ""
                                for vi, v1 in enumerate(cons1_value):
                                    if key == cons1_keys[vi] and v1 == v2:
                                        interact_cons1_value.append(v1)
                                        last = ""
                                        break
                                    elif key == cons1_keys[vi] and v1 != v2:
                                        last = v1
                                if last != "":
                                    interact_cons1_value.append(last)
                            cons1_keys = interact_cons1_keys
                            cons1_value = interact_cons1_value
                        if interact_same:
                            continue
                        else:
                            general_diff = False
                            other_diff_idx = []
                            for vi, v1 in enumerate(cons1_value):
                                v2 = cons2_value[vi]
                                if v1 != v2 and cons1_keys[vi] in general_keys:
                                    general_diff = True
                                    break
                                elif v1 != v2 and cons1_keys[vi] not in general_keys:
                                    other_diff_idx.append(vi)
                            if general_diff:
                                # 不冲突
                                continue
                            else:
                                # 冲突
                                reason = f"规则{id1}和{id2}的结果相同，但存在互相冲突的约束：对规则{id1}，"
                                for idx in other_diff_idx:
                                    reason += f"{cons1_keys[idx]}为{cons1_value[idx]}，"
                                reason += f"而对规则{id2}，"
                                for idx in other_diff_idx:
                                    reason += f"{cons2_keys[idx]}为{cons2_value[idx]}，"
                                reason = f"{reason[:-1]}。"
                                conflict_rules.append({"rule_ids":[id1, id2], "reason":reason})

                    elif interact:
                        continue
                    else:
                        continue


            else:
                if if_same:
                    # 冲突
                    conflict_rules.append({"rule_ids":[id1, id2], "reason":f"规则{id1}和{id2}的约束相同，但却产生了不同的结果"})
                else:
                    # 判断cons1的key和cons2的key之间的关系
                    cons1_keys, cons2_keys = [con['key'] for con in cons1], [con['key'] for con in cons2]
                    cons1_value, cons2_value = [con['value'] for con in cons1], [con['value'] for con in cons2]
                    # 统计两个规则中的每个key的数量
                    count1, count2 = {}, {}
                    for key in cons1_keys:
                        if key in count1:
                            count1[key] += 1
                        else:
                            count1[key] = 1
                    for key in cons2_keys:
                        if key in count2:
                            count2[key] += 1
                        else:
                            count2[key] = 1
                    cons1_in_cons2, cons2_in_cons1, interact = True, True, False
                    for key in list(count1.keys()):
                        if key in count2:
                            interact = True
                        elif key in count2 and count1[key] != count2[key] or key not in count2:
                            cons1_in_cons2 = False
                    for key in list(count2.keys()):
                        if key in count1 and count1[key] != count2[key] or key not in count1:
                            cons2_in_cons1 = False
                            break
                    
                    if cons1_in_cons2 and cons2_in_cons1:
                        continue
                    elif cons1_in_cons2 or cons2_in_cons1:
                        # 判断相交部分的value是否完全相同
                        interact_same = True
                        if cons1_in_cons2:
                            for ki, key1 in enumerate(cons1_keys):
                                kv_diff = True
                                for kj, key2 in enumerate(cons2_keys):
                                    if key1 == key2 and cons1_value[ki] == cons2_value[kj]:
                                        kv_diff = False
                                        break
                                if kv_diff:
                                    interact_same = False
                                    break
                            # 将cons2_keys和cons2_value设置为交集部分
                            interact_cons2_keys = copy.deepcopy(cons1_keys)
                            interact_cons2_value = []
                            for ki, key in enumerate(interact_cons2_keys):
                                v1 = cons1_keys[ki]
                                last = ""
                                for vi, v2 in enumerate(cons2_value):
                                    if key == cons2_keys[vi] and v1 == v2:
                                        interact_cons2_value.append(v1)
                                        last = ""
                                        break
                                    elif key == cons2_keys[vi] and v1 != v2:
                                        last = v2
                                if last != "":
                                    interact_cons2_value.append(last)
                            cons2_keys = interact_cons2_keys
                            cons2_value = interact_cons2_value
                        else:
                            for ki, key2 in enumerate(cons2_keys):
                                kv_diff = True
                                for kj, key1 in enumerate(cons1_keys):
                                    if key1 == key2 and cons1_value[kj] == cons2_value[ki]:
                                        kv_diff = False
                                        break
                                if kv_diff:
                                    interact_same = False
                                    break
                            # 将cons1_keys和cons1_value设置为交集部分
                            interact_cons1_keys = copy.deepcopy(cons2_keys)
                            interact_cons1_value = []
                            for ki, key in enumerate(interact_cons1_keys):
                                v2 = cons2_keys[ki]
                                last = ""
                                for vi, v1 in enumerate(cons1_value):
                                    if key == cons1_keys[vi] and v1 == v2:
                                        interact_cons1_value.append(v1)
                                        last = ""
                                        break
                                    elif key == cons1_keys[vi] and v1 != v2:
                                        last = v1
                                if last != "":
                                    interact_cons1_value.append(last)
                            cons2_keys = interact_cons1_keys
                            cons2_value = interact_cons1_value
                        if interact_same:
                            # 冲突
                            if len(cons1_keys) > len(cons2_keys):
                                reason = f"规则{id2}的约束包含规则{id1}，但它们的结果不一致"
                            else:
                                reason = f"规则{id1}的约束包含规则{id2}，但它们的结果不一致"
                            conflict_rules.append({"rule_ids": [id1, id2], "reason":reason})
                        else:
                            continue
                    
                    elif interact:
                        continue
                    else:
                        continue
    return conflict_rules


if __name__ == "__main__":
    input_data = json.load(open("rules_cache/consistency_checking_input.json", "r", encoding="utf-8"))
    conflict_rules = consistency_checking(input_data['data'])
    pprint.pprint(conflict_rules)



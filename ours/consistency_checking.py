import json
import pprint
from transfer.mydsl_to_rules import mydsl_to_rules
import copy
from ours.process_r1_to_r2 import is_num_key, is_price_key, is_time_key
from ours.process_r3_to_testcase import isnumber, gen_cons, gen_temp_v
import re
import z3


def process_result_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys):
    # TODO 这个地方存疑，1、是否冲突的时间、数量、价格必须是数值变量（目前是）；2、如果存在两个或更多时间、数量、价格冲突，规则是否冲突（目前不冲突）。
    if cons1_value == cons2_value:
        return False, {}
    general_diff = False  # 是否是通用的key不同
    other_diff_idx = []  # 不同的key的index
    for vi, v1 in enumerate(cons1_value):
        v2 = cons2_value[vi]
        if v1 != v2: 
            # 时间、数量、价格不同，并且是数值型变量
            if (is_time_key(cons1_keys[vi]) or is_num_key(cons1_keys[vi]) or is_price_key(cons1_keys[vi])):
                if (isinstance(v1, list) or len(re.findall(r"\d+", v1)) > 0) and (isinstance(v2, list) or len(re.findall(r"\d+", v2)) > 0):
                    other_diff_idx.append(vi)
                    continue
                else:
                    general_diff = True
                    break
            elif cons1_keys[vi] not in general_keys:
                other_diff_idx.append(vi)
                continue
            # 枚举约束，通用key不同
            else:
                general_diff = True
                break
    
    if general_diff or len(other_diff_idx) >= 2:
        # 不冲突
        return False, {}
    else:
        # 冲突
        reason = f"规则{id1}和{id2}的结果相同，但存在互相冲突的约束：对规则{id1}，"
        for idx in other_diff_idx:
            reason += f"{cons1_keys[idx]}{' ' + ' '.join(cons1_value[idx]) if isinstance(cons1_value[idx], list) else '为' + cons1_value[idx]}，"
        reason += f"而对规则{id2}，"
        for idx in other_diff_idx:
            reason += f"{cons2_keys[idx]}{' ' + ' '.join(cons2_value[idx]) if isinstance(cons2_value[idx], list) else '为' + cons2_value[idx]}，"
        reason = f"{reason[:-1]}。"
        return True, {"rule_ids":[id1, id2], "reason":reason}



def process_result_not_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys):
    # TODO 这个地方存疑，1、是否冲突的时间、数量、价格必须是数值变量；2、如果存在两个或更多时间、数量、价格冲突，规则是否冲突。
    if cons1_value == cons2_value:
        return True, {"rule_ids":[id1, id2], "reason":f"规则{id1}和{id2}的约束可以实例化为相同，但却产生了不同的结果"}
    general_diff = False  # 是否是通用的key不同
    other_diff_idx = []  # 不同的key的index
    for vi, v1 in enumerate(cons1_value):
        v2 = cons2_value[vi]
        if v1 != v2: 
            # 时间、数量、价格不同，并且是数值型变量，并且有交集
            if (is_time_key(cons1_keys[vi]) or is_num_key(cons1_keys[vi]) or is_price_key(cons1_keys[vi])):
                if (isinstance(v1, list) or len(re.findall(r"\d+", v1)) > 0) and (isinstance(v2, list) or len(re.findall(r"\d+", v2)) > 0) and intersection(is_time_key(cons1_keys[vi]), is_num_key(cons1_keys[vi]), is_price_key(cons1_keys[vi]), v1, v2):
                    other_diff_idx.append(vi)
                    continue
                else:
                    general_diff = True
                    break
            # 一个匿名成功，一个显名失败，不冲突
            # elif cons1_keys[vi] not in general_keys:
            #     other_diff_idx.append(vi)
            #     continue
            # 枚举约束，通用key不同
            else:
                general_diff = True
                break
        
    if general_diff:
        # 不冲突
        return False, {}
    else:
        # 冲突
        reason = f"规则{id1}和{id2}的结果不同，但存在互相冲突的约束：对规则{id1}，"
        for idx in other_diff_idx:
            reason += f"{cons1_keys[idx]}{' ' + ' '.join(cons1_value[idx]) if isinstance(cons1_value[idx], list) else '为' + cons1_value[idx]}，"
        reason += f"而对规则{id2}，"
        for idx in other_diff_idx:
            reason += f"{cons2_keys[idx]}{' ' + ' '.join(cons2_value[idx]) if isinstance(cons2_value[idx], list) else '为' + cons2_value[idx]}，"
        reason = f"{reason[:-1]}。"
        return True, {"rule_ids":[id1, id2], "reason":reason}




def intersection(time_key, num_key, price_key, v1, v2):
    if time_key:
        if "{[" in v1 and "{[" in v2:
            v1, v2 = v1[2:-2], v2[2:-2]
        elif "[" in v1 and "[" in v2:
            v1, v2 = v1[1:-1], v2[1:-1]
        v5 = v2
        print(v1, v2)
        v1, v2 = v1.split("-")[0], v1.split("-")[1]
        v3, v4 = v5.split("-")[0], v5.split("-")[1]
        v1 = "0" + v1 if len(v1) == 4 else v1
        v2 = "0" + v2 if len(v2) == 4 else v2
        v3 = "0" + v3 if len(v3) == 4 else v3
        v4 = "0" + v4 if len(v4) == 4 else v4
        if v2 <= v3 or v4 <= v1:  # 无交集
            return False
        else:
            return True
    elif num_key:
        return SMT_Solver(v1, v2, "num")
    elif price_key:
        return SMT_Solver(v1, v2, "price")
    return False


def SMT_Solver(v1, v2, task):  # 如果有解，返回True，否则返回False
    if task == "num":
        variable = z3.Int("variable")
    else:
        variable = z3.Real("variable")
    cons = []
    cons.append(variable > 0)
    if len(v1) == 2:
        op, value = v1[0], v1[1]
        if isnumber(value):
            cons.append(gen_cons(op, variable, value))
        else:
            value = 100  # 变量实例化
            cons.append(gen_cons(op, variable, value))
    elif len(v1) == 4:
        op1, value1, op2, value2 = value[:]
        if not isnumber(value1):
            value1 = 100000
        if not isnumber(value2):
            value2 = 0
        cons.append(gen_cons(op2, gen_temp_v(op1, variable, value1), value2))
    else:
        return False
    if len(v2) == 2:
        op, value = v2[0], v2[1]
        if isnumber(value):
            cons.append(gen_cons(op, variable, value))
        else:
            value = 100  # 变量实例化
            cons.append(gen_cons(op, variable, value))
    elif len(v2) == 4:
        op1, value1, op2, value2 = v2[:]
        if not isnumber(value1):
            value1 = 100000
        if not isnumber(value2):
            value2 = 0
        cons.append(gen_cons(op2, gen_temp_v(op1, variable, value1), value2))
    else:
        return False
    solver = z3.Solver()
    for con in cons:
        solver.push()
        solver.add(con)
    return solver.check() == z3.sat


def instantiate(cons1_keys, cons1_value, cons2_keys, cons2_value, then_same):
    # 实例化为特例，并按照key相同比较
    # 如果遇到重复的key，value合并，最后len应该相同
    new_con1_keys, new_cons1_value = [], []
    for index, key in enumerate(cons1_keys):
        value = cons1_value[index]
        if key not in new_con1_keys:
            new_con1_keys.append(key)
            new_cons1_value.append(value)
        else:
            for index1, k in enumerate(new_con1_keys):
                if k == key:
                    if isinstance(new_cons1_value[index1], list) and isinstance(value, str):
                        ...
                    elif isinstance(new_cons1_value[index1], str) and isinstance(value, list):
                        new_cons1_value[index1] = value
                    else:
                        new_cons1_value[index1] = new_cons1_value[index1] + value
                    break
    cons1_keys, cons1_value = new_con1_keys, new_cons1_value
    new_con2_keys, new_cons2_value = [], []
    for index, key in enumerate(cons2_keys):
        value = cons2_value[index]
        if key not in new_con2_keys:
            new_con2_keys.append(key)
            new_cons2_value.append(value)
        else:
            for index2, k in enumerate(new_con2_keys):
                if k == key:
                    if isinstance(new_cons2_value[index2], list) and isinstance(value, str):
                        ...
                    elif isinstance(new_cons2_value[index2], str) and isinstance(value, list):
                        new_cons2_value[index2] = value
                    else:
                        new_cons2_value[index2] = new_cons2_value[index2] + value
                    break
    cons2_keys, cons2_value = new_con2_keys, new_cons2_value
    
    union = list(set(cons1_keys + cons2_keys))
    if then_same:
        new_cons1_value = []
        for key in union:
            find = False
            for index, key1 in enumerate(cons1_keys):
                if key == key1:
                    new_cons1_value.append(cons1_value[index])
                    find = True
                    break
            if not find:
                for index, key1 in enumerate(cons2_keys):
                    if key == key1:
                        new_cons1_value.append(cons2_value[index])
                        break
        cons1_keys = copy.deepcopy(union)
        cons1_value = new_cons1_value


        new_cons2_value = []
        for key in union:
            find = False
            for index, key1 in enumerate(cons2_keys):
                if key == key1:
                    new_cons2_value.append(cons2_value[index])
                    find = True
                    break
            if not find:
                for index, key1 in enumerate(cons1_keys):
                    if key == key1:
                        new_cons2_value.append(cons1_value[index])
                        break
        cons2_keys = copy.deepcopy(union)
        cons2_value = new_cons2_value

    else:
        new_cons1_value = []
        not_conflict = False
        for key in union:
            find = False
            for index, key1 in enumerate(cons1_keys):
                if key == key1:
                    new_cons1_value.append(cons1_value[index])
                    find = True
                    break
            if not find:
                if is_num_key(key) or is_time_key(key) or is_price_key(key):
                    not_conflict = True
                    break
                for index, key1 in enumerate(cons2_keys):
                    if key == key1:
                        new_cons1_value.append(cons2_value[index])
                        break
        if not not_conflict:
            cons1_keys = copy.deepcopy(union)
            cons1_value = new_cons1_value


        new_cons2_value = []
        not_conflict = False
        for key in union:
            find = False
            for index, key1 in enumerate(cons2_keys):
                if key == key1:
                    new_cons2_value.append(cons2_value[index])
                    find = True
                    break
            if not find:
                if is_num_key(key) or is_time_key(key) or is_price_key(key):
                    not_conflict = True
                    break
                for index, key1 in enumerate(cons1_keys):
                    if key == key1:
                        new_cons2_value.append(cons1_value[index])
                        break
        if not not_conflict:
            cons2_keys = copy.deepcopy(union)
            cons2_value = new_cons2_value


        for index, key in enumerate(cons2_keys):
            value = cons2_value[index]
            if key not in cons1_keys:
                if is_num_key(key) or is_time_key(key) or is_price_key(key):
                    break
                else:
                    cons1_keys.insert(index, key)
                    cons1_value.insert(index, value)
        for index, key in enumerate(cons1_keys):
            value = cons1_value[index]
            if key not in cons2_keys:
                if is_num_key(key) or is_time_key(key) or is_price_key(key):
                    break
                else:
                    cons2_keys.insert(index, key)
                    cons2_value.insert(index, value)


    return cons1_keys, cons1_value, cons2_keys, cons2_value




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
            cons1, cons2, res1, res2 = sorted(rule1['constraints'], key=lambda x:x['key']), sorted(rule2['constraints'], key=lambda x:x['key']), [rs for rs in sorted(rule1['results'], key=lambda x:x['key']) if rs['key'] != "状态"], [rs for rs in sorted(rule2['results'], key=lambda x:x['key']) if rs['key'] != "状态"]

            
            # 这里的if_same，then_same都是完全相同的意思
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
                else:  # if不同，then相同
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
                    
                    if cons1_in_cons2 and cons2_in_cons1:  # key相同，如果general key的value不同，不冲突；否则，如果为时间数量价格的value不同且value不为枚举约束，则冲突
                        if_conflict, info = process_result_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys)
                        if if_conflict:
                            conflict_rules.append(info)
                    
                    elif cons1_in_cons2 or cons2_in_cons1:

                        cons1_keys, cons1_value, cons2_keys, cons2_value = instantiate(cons1_keys, cons1_value, cons2_keys, cons2_value, then_same)
                        assert cons1_keys == cons2_keys and len(cons2_keys) == len(cons2_value) == len(cons1_keys) == len(cons1_value)

                        if_conflict, info = process_result_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys)
                        if if_conflict:
                            conflict_rules.append(info)

                    elif interact:
                        # cons1_keys, cons1_value, cons2_keys, cons2_value = instantiate(cons1_keys, cons1_value, cons2_keys, cons2_value, then_same)
                        # assert cons1_keys == cons2_keys and len(cons2_keys) == len(cons2_value) == len(cons1_keys) == len(cons1_value)

                        # if_conflict, info = process_result_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys)
                        # if if_conflict:
                        #     conflict_rules.append(info)
                        continue
                    else:
                        continue


            else:  # then不同
                if if_same:
                    # 冲突
                    conflict_rules.append({"rule_ids":[id1, id2], "reason":f"规则{id1}和{id2}的约束相同，但却产生了不同的结果"})
                else:  # if和then都不同
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
                        # key相同，如果general key的value不同，不冲突；否则，如果为时间数量价格的value不同且value不为枚举约束，且约束有重合的地方，则冲突（重合的地方不知是成功还是失败）
                        if_conflict, info = process_result_not_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys)
                        if if_conflict:
                            conflict_rules.append(info)

                    elif cons1_in_cons2 or cons2_in_cons1:
                        cons1_keys, cons1_value, cons2_keys, cons2_value = instantiate(cons1_keys, cons1_value, cons2_keys, cons2_value, then_same)
                        
                        if not (cons1_keys == cons2_keys and len(cons2_keys) == len(cons2_value) == len(cons1_keys) == len(cons1_value)):
                            # 不冲突
                            continue

                        if_conflict, info = process_result_not_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys)
                        if if_conflict:
                            conflict_rules.append(info)
                    
                    elif interact:
                        # cons1_keys, cons1_value, cons2_keys, cons2_value = instantiate(cons1_keys, cons1_value, cons2_keys, cons2_value, then_same)
                        # if not (cons1_keys == cons2_keys and len(cons2_keys) == len(cons2_value) == len(cons1_keys) == len(cons1_value)):
                        #     # 不冲突
                        #     continue
                        
                        # if_conflict, info = process_result_not_same_key_same(id1, id2, cons1_keys, cons2_keys, cons1_value, cons2_value, general_keys)
                        # if if_conflict:
                        #     conflict_rules.append(info)
                        continue
                    else:
                        continue
    return conflict_rules


if __name__ == "__main__":
    input_data = json.load(open("cache/consistency_checking_input.json", "r", encoding="utf-8"))
    conflict_rules = consistency_checking(input_data['data'])
    pprint.pprint(conflict_rules)



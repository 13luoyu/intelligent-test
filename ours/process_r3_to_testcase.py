import collections
import re
import z3
import pprint

from ours.process_tco_to_r1 import is_time_key, is_num_key, is_price_key

'''tsy修改：346行'''


def testcase(defines, vars, rules):
    vars = list_conditions(defines, vars, rules)
    # pprint.pprint(vars)
    return vars



def isnumber(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


def list_conditions(defines, vars, rules):
    """依据rules中的规则，枚举部分可能出现的条件，将枚举结果写入vars"""
    # 将操作中的“买入”、“卖出”转为申报
    for rule_id in rules:
        rule = rules[rule_id]
        for c in rule['constraints']:
            if c['key'] == "操作" and (c['value'] == "买入" or c['value'] == "卖出"):
                c['value'] = "申报"
    conflict_to_delete = []
    for rule_id in rules:
        rule = rules[rule_id]
        for result in rule['results']:
            if result['key'] == "状态":
                rule['constraints'].append({"key":"结果状态", "operation":"is", "value":result['value']})
                vars[rule_id]["结果状态"] = []
                break
        constraints = rule["constraints"]
        # 存储所有用z3求解的z3格式约束
        cons = dict()  # cons[条件名] = [条件列表]
        # 存储所有z3变量
        variables = dict()  # variables[条件名] = [z3条件变量]
        time_constraints = []
        for cnt, c in enumerate(constraints):
            if "operation" not in c:
                c["operation"] = "is"
            key = c["key"]
            op = c["operation"]
            value = c["value"]

            # part 1 连接词是 is
            # 规则是仅将这个值加入vars，不考虑其他值
            # 如果该key已经存在，则序号递增，如操作，操作2，操作3...
            opposite_tnp = True
            if op == "is":
                real_key = key
                if len(vars[rule_id][key]) > 0:
                    index = 2
                    while f"{key}{index}" in vars[rule_id]:
                        index += 1
                    if opposite_tnp and index > 3:
                        conflict_to_delete.append(rule_id)
                        break
                    vars[rule_id][f"{key}{index}"] = [value]
                    real_key = f"{key}{index}"
                else:
                    vars[rule_id][key].append(value)
                # 这个地方用于生成时间、数量、价格的枚举变量的反，但如果不注释掉，生成测试用例非常多
                if opposite_tnp and (is_time_key(key) or is_num_key(key) or is_price_key(key)):
                    if "不" in value:
                        value = value[value.find("不")+1:]
                    else:
                        value = "非" + value
                    vars[rule_id][real_key] = [[vars[rule_id][real_key][0]], [value]]

            # part 2 连接词是 in
            elif op == "in":
                if ':' in value and '-' in value:
                    value = value[1:-1].split(',')
                    for i, v in enumerate(value):
                        value[i] = v.strip()
                    v = value[0]
                elif value in defines:
                    value = defines[value]
                    v = value[0]
                else:
                    continue

                # v是一个时间，形式有以下这些种，即 12:00:00, 9:00:00, 09:00:00, 12:00, 9:00, 09:00,
                # 9:00-12:00, 09:00:00-12:00:00等
                if re.match("\[\d{1,2}:\d{2}:\d{2}-\d{1,2}:\d{2}:\d{2}\]", v) \
                        or re.match("\[\d{1,2}:\d{2}-\d{1,2}:\d{2}\]", v):
                    # [[时:分:秒-时:分:秒], ]数组，转化成[[时:分:秒-时:分:秒], ]数组
                    if re.match("\[\d{1,2}:\d{2}:\d{2}-\d{1,2}:\d{2}:\d{2}\]", v):
                        new_value = []
                        for v in value:
                            v = v[1:-1]  # v = 9:15:00-11:30:00
                            s = ""
                            for vi in v.split("-"):
                                if len(vi) < 8:
                                    s += "0" + vi
                                else:
                                    s += vi
                                s += "-"
                            new_value.append("[" + s[:-1] + "]")
                        new_value.sort()
                        value = new_value
                    # [[时:分-时:分], ]数组，转化成[[时:分:秒-时:分:秒], ]数组
                    elif re.match("\[\d{1,2}:\d{2}-\d{1,2}:\d{2}\]", v):
                        new_value = []
                        for v in value:
                            v = v[1:-1]  # v = 9:15-11:30
                            s = ""
                            for vi in v.split("-"):
                                if len(vi) < 5:
                                    s += "0" + vi + ":00"
                                else:  # len(v) == 5
                                    s += vi + ":00"
                                s += "-"
                            new_value.append("[" + s[:-1] + "]")
                        new_value.sort()
                        value = new_value
                    time_constraints += value
                    vars[rule_id][key] = [value]

                # 如果仅有一个元素v，那么添加值为v，非v
                elif len(value) == 1:
                    vars[rule_id][key].append(v)
                    vars[rule_id][key].append("非" + v)

            # part 3 这是一个表达式计算约束
            elif op == "compute":
                if key not in cons:
                    cons[key] = []
                if len(value) == 2:  # a >= 100000
                    op1 = value[0]
                    value = value[1]
                    if key in variables:
                        variable = variables[key]
                    else:
                        if '.' in value and re.match("[\d]*.[\d]*[1-9]", value):
                            variable = z3.Real(key)
                        else:
                            variable = z3.Int(key)
                        variables[key] = variable
                        cons[key].append(variable > 0)
                    if isnumber(value):
                        value = float(value)
                        cc = gen_cons(op1, variable, value)
                        cons[key].append(cc)

                    else:  # value不是一个数字，考虑value是否在defines中定义
                        if value in defines and len(defines[value]) == 1:
                            if isnumber(defines[value][0]):
                                value = float(defines[value][0])
                                cc = gen_cons(op1, variable, value)
                                cons[key].append(cc)
                                continue
                            else:
                                value = defines[value][0]
                        if len(vars[rule_id][key]) == 0:
                            vars[rule_id][key] = [[], []]
                        if op1 == "<":
                            vars[rule_id][key][0].append("小于" + value)
                            vars[rule_id][key][1].append("不低于" + value)
                        elif op1 == ">=":
                            vars[rule_id][key][0].append("不低于" + value)
                            vars[rule_id][key][1].append("小于" + value)
                        elif op1 == "<=":
                            vars[rule_id][key][0].append("不超过" + value)
                            vars[rule_id][key][1].append("大于" + value)
                        elif op1 == ">":
                            vars[rule_id][key][0].append("大于" + value)
                            vars[rule_id][key][1].append("不超过" + value)
                        elif op1 == "==":
                            vars[rule_id][key][0].append(value)
                            vars[rule_id][key][1].append("非" + value)
                        elif op1 == "!=":
                            vars[rule_id][key][0].append("非" + value)
                            vars[rule_id][key][1].append(value)
                        del cons[key]
                        if key in variables:
                            del variables[key]

                elif len(value) == 4:  # a % 100000 == 0
                    op1, value1, op2, value2 = value[:]
                    if key in variables:
                        variable = variables[key]
                    else:
                        variable = z3.Int(key)
                        variables[key] = variable
                        cons[key].append(variable > 0)
                    if not isnumber(value1):
                        if value1 in defines and len(defines[value1]) == 1 and isnumber(defines[value1][0]):
                            value1 = defines[value1][0]
                        else:  # 未定义情况
                            continue
                    value1 = float(value1) if '.' in value1 else int(value1)
                    if not isnumber(value2):
                        if value2 in defines and len(defines[value2]) == 1 and isnumber(defines[value2][0]):
                            value2 = defines[value2][0]
                        else:  # 未定义情况
                            continue
                    value2 = float(value2) if '.' in value2 else int(value2)
                    if op1 in ['+', '-', '*', '/', '%']:  # a % 100000 == 0
                        v1 = gen_temp_v(op1, variable, value1)
                        cc = gen_cons(op2, v1, value2)
                    else:  # 暂未使用
                        v1 = gen_temp_v(op2, value1, value2)
                        cc = gen_cons(op1, variable, v1)
                    cons[key].append(cc)

                elif len(value) == 6:  # a%100000==b%100000
                    key = c["key"]
                    op1, value1, op2, value2, op3, value3 = c["value"]
                    # print(c["value"])
                    if not isnumber(value1):
                        if value1 in defines:
                            vars[rule_id][value1] = []
                            vars[rule_id][value1].append(defines[value1][0])
                            value1 = defines[value1][0]
                        else:
                            raise ValueError(f"常量{value1}未定义")
                    value1 = float(value1) if '.' in value1 else int(value1)
                    if not isnumber(value2):
                        if value2 in defines:
                            vars[rule_id][value2] = []
                            vars[rule_id][value2].append(defines[value2][0])
                            value2 = defines[value2][0]
                        else:
                            raise ValueError(f"常量{value2}未定义")
                    value2 = float(value2) if '.' in value2 else int(value2)
                    if not isnumber(value3):
                        if value3 in defines:
                            vars[rule_id][value3] = []
                            vars[rule_id][value3].append(defines[value3][0])
                            value3 = defines[value3][0]
                        else:
                            raise ValueError(f"常量{value3}未定义")
                    value3 = float(value3) if '.' in value3 else int(value3)
                    value = gen_temp_v(op3, value2, value3)
                    # cons[key].append(gen_cons(op2, gen_temp_v(op1, variable, value1), value))
                    # 求解器生成的不能令人满意，直接手动生成
                    vars[rule_id][key] = [[], []]
                    vars[rule_id][key][0].append(value2 % value3)
                    vars[rule_id][key][0].append(value2 - value3)
                    vars[rule_id][key][1].append(int(value2 - value3 / 10))
                    vars[rule_id][key][1].append(int(value3 / 10))

        if rule_id in conflict_to_delete:
            continue
        if len(time_constraints) == 1:
            for idc, c in enumerate(rules[rule_id]['constraints']):
                if is_time_key(c['key']):
                    del rules[rule_id]['constraints'][idc]
                    del vars[rule_id][c['key']]
                    break
        if len(time_constraints) > 0:
            # 生成正时间、反时间
            time_constraints = sorted(time_constraints)
            value = []
            done = False
            for ti, t in enumerate(time_constraints):
                if done:
                    done = False
                    continue
                if ti+1 < len(time_constraints):
                    t1 = t.split("-")[1][:-1]
                    t2 = time_constraints[ti+1].split("-")[0][1:]
                    if t1 >= t2:
                        t = t.split("-")[0] + "-" + time_constraints[ti+1].split("-")[1]
                        value.append(t)
                        done = True
                    else:
                        value.append(t)
                else:
                    value.append(t)
            # if len(value) == 2:
            #     value = [value[0][:-1] + "," + value[1][1:]]
            # elif len(value) >= 3:
            #     value1 = value[0][:-1]
            #     for i in range(1, len(value)-1, 1):
            #         value1 += "," + value[i][1:-1]
            #     value1 += "," + value[-1][1:]
            #     value = [value1]
            not_valid_value = []  # value的补集
            last = "00:00:00"
            last_valid = False
            for v in value:
                for vi in v[1:-1].split("-"):
                    if not last_valid and last != vi:
                        not_valid_value.append("[" + last + "-" + vi + "]")
                    last = vi
                    last_valid = ~last_valid
            if last != "24:00:00":
                not_valid_value.append("[" + last + "-" + "24:00:00" + "]")
            # if len(not_valid_value) == 2:
            #     not_valid_value = [not_valid_value[0][:-1] + "," + not_valid_value[1][1:]]
            # elif len(not_valid_value) >= 3:
            #     value1 = not_valid_value[0][:-1]
            #     for i in range(1, len(not_valid_value)-1, 1):
            #         value1 += "," + not_valid_value[i][1:-1]
            #     value1 += "," + not_valid_value[-1][1:]
            #     not_valid_value = value1
            vars[rule_id]["交易时间"] = [value, not_valid_value]

        
        # 生成单变量
        if len(cons) > 0:
            # print(cons)
            rs = judge_conflict_and_generate_value(variables, cons, rule_id, vars)
            if not rs:
                conflict_to_delete.append(rule_id)

            

    for id in conflict_to_delete:
        if id in vars:
            del vars[id]
        if id in rules:
            del rules[id]

    return vars


def gen_cons(op, a, b):
    if op == "<":
        return a < b
    elif op == "<=":
        return a <= b
    elif op == ">":
        return a > b
    elif op == ">=":
        return a >= b
    elif op == "==":
        return a == b
    elif op == "!=":
        return a != b


def gen_temp_v(op, a, b):
    if op == "+":
        v1 = a + b
    elif op == "-":
        v1 = a - b
    elif op == "*":
        v1 = a * b
    elif op == "/":
        v1 = a / b
    elif op == "%":
        v1 = a % b
    return v1


def judge_conflict_and_generate_value(variables, cons, rule_id, vars):
    rss = []
    for variable in variables:
        # 如果条件本社就是矛盾的，直接退出
        if_conflict = judge_if_conflict(cons[variable])
        if if_conflict:
            return False
        solver = z3.Solver()
        for con in cons[variable]:
            solver.push()
            solver.add(con)
        # 先生成一个成功的案例
        if solver.check() == z3.sat:
            rs = solver.model()
            value = int(rs[variables[variable]].as_long()) if isinstance(rs[variables[variable]], z3.IntNumRef) else float(rs[variables[variable]].as_decimal(prec=6)[:6])
            rs = [value]
        # 生成多个案例，包含一个成功，其余失败
        solver = z3.Solver()
        solver.add(variables[variable] > 0)
        solver.add(variables[variable] != rs[0])
        rs += generate_value(solver, cons[variable], 0, variables[variable])
        rss.append(rs)

    for i, key in enumerate(variables):
        valid_value = []
        not_valid_value = []
        for j, r in enumerate(rss[i]):
            if j == 0 or (len(rss[i]) > 2 and j == 1):
                valid_value.append(r)
            else:
                not_valid_value.append(r)
        vars[rule_id][key] = [valid_value, not_valid_value]
    '''增加一次性申报特殊判定'''
    # 案例
    # 成功：
    # 余额10000，卖出10000
    # 余额20000，卖出20000
    # 余额110000，卖出110000
    # 余额110000，卖出100000
    # 失败：
    # 余额20000，卖出10000
    # 余额220000，卖出110000
    if "操作" in vars[rule_id].keys() and "次性" in vars[rule_id]['操作'][0]:
        if "数量" in vars[rule_id] and "申报数量" in vars[rule_id]:
            del vars[rule_id]['数量']
            key = "申报数量"
        elif "数量" in vars[rule_id] and "申报数量" not in vars[rule_id]:
            key = "数量"
        elif "数量" not in vars[rule_id]:
            key = "申报数量"
        if "余额" in vars[rule_id]:
            del vars[rule_id]['余额']
        zero_num = 0
        for old_key in list(vars[rule_id]):
            if key in old_key:
                break
        if len(vars[rule_id][old_key]) > 1:
            for num in vars[rule_id][old_key][1]:
                x=len(str(num))-1
                zero_num = max(zero_num, x)
            valid_value = [f"{10**(zero_num-1)}(余额{10**(zero_num-1)})", f"{2*10**(zero_num-1)}(余额{2*10**(zero_num-1)})", f"{11*10**(zero_num-1)}(余额{11*10**(zero_num-1)})", f"{11*10**(zero_num-1)}(余额{10*10**(zero_num-1)})"]
            not_valid_value = [f"{2*10**(zero_num-1)}(余额{10**(zero_num-1)})", f"{22*10**(zero_num-1)}(余额{11*10**(zero_num-1)})"]
            del vars[rule_id][old_key]
            vars[rule_id][key] = [valid_value, not_valid_value]
    return True


def generate_value(s, cons, begin, var):
    """
    枚举所有cons成立和不成立的组合，并使用求解器获得测试样例
    :param s: Solver求解器
    :param cons: 条件数组
    :param begin: 条件的序号
    :param var: 单个z3变量
    :return: 测试值
    """
    if len(cons) == begin:
        if s.check() == z3.sat:
            rs = s.model()
            value = int(rs[var].as_long()) if isinstance(rs[var], z3.IntNumRef) else float(rs[var].as_decimal(prec=6)[:6])
            return [value]
        else:
            return []

    s.push()
    s.add(cons[begin])
    rs1 = generate_value(s, cons, begin + 1, var)
    s.pop()
    s.add(z3.Not(cons[begin]))
    rs2 = generate_value(s, cons, begin + 1, var)
    return rs1 + rs2


def judge_if_conflict(cons):
    s = z3.Solver()
    for con in cons:
        s.push()
        s.add(con)
    if s.check() == z3.sat:
        return False
    return True



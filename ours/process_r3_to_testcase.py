import collections
import re
import z3
import pprint

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
    conflict_to_delete = []
    for rule_id in rules:
        rule = rules[rule_id]
        constraints = rule["constraints"]
        # 存储所有用z3求解的z3格式约束
        cons = dict()  # cons[条件名] = [条件列表]
        # 存储所有z3变量
        variables = dict()  # variables[条件名] = [z3条件变量]
        # 像sum(a)>=b这样的要求，放到最后做，这里先记录
        wait_dic = collections.OrderedDict()  # wait_dic[条件名] = [c]
        # cons的原始约束，和下面的wait_var_dic一起用
        cons_detail = {}  # cons_detail[条件名] = [c]
        # 有些变量需要像sum(a)这样的求解之后才能赋值，这里记录下来(边界价格 = max()，需要先算max())
        wait_var_dic = {}  # wait_var_dic[条件名] = c
        for cnt, c in enumerate(constraints):
            # print("--------------"+str(cnt)+"-----------------")
            # print(c)
            if "operation" not in c:
                c["operation"] = "is"
            key = c["key"]
            op = c["operation"]
            value = c["value"]

            # part 1 连接词是 is
            # 规则是仅将这个值加入vars，不考虑其他值
            if op == "is":
                # print(rule_id)
                vars[rule_id][key].append(value)

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
                    not_valid_value = []  # value的补集
                    last = "00:00:00"
                    last_valid = False
                    for v in value:
                        for vi in v[1:-1].split("-"):
                            if not last_valid:
                                not_valid_value.append("[" + last + "-" + vi + "]")
                            last = vi
                            last_valid = ~last_valid
                    not_valid_value.append("[" + last + "-" + "24:00:00" + "]")
                    vars[rule_id][key] = [value, not_valid_value]

                # 如果仅有一个元素v，那么添加值为v，非v
                elif len(value) == 1:
                    vars[rule_id][key].append(v)
                    vars[rule_id][key].append("非" + v)

            # part 3 这是一个表达式计算约束
            elif op == "compute":
                # print("--------------"+str(cnt)+"-----------------")
                # print(c, cons)
                if key not in cons:
                    cons[key] = []
                if len(value) == 2:
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
                        if key not in cons_detail:
                            cons_detail[key] = []
                        cons_detail[key].append(c)

                    else:  # value不是一个数字，考虑value是一个变量，是一个常量，还是未定义
                        if value in defines:  # 定义在define中，可能是常量或未定义
                            v = defines[value]
                            if len(v) == 0:  # 未定义
                                if len(vars[rule_id][key]) == 0:
                                    vars[rule_id][key] = [[], []]
                                if op1 == "<":
                                    vars[rule_id][key][0].append(value + "之前")
                                    vars[rule_id][key][1].append(value + "及" + value + "之后")
                                elif op1 == ">=":
                                    vars[rule_id][key][0].append(value + "及" + value + "之后")
                                    vars[rule_id][key][1].append(value + "之前")
                                elif op1 == "<=":
                                    vars[rule_id][key][0].append(value + "及" + value + "之前")
                                    vars[rule_id][key][1].append(value + "之后")
                                elif op1 == ">":
                                    vars[rule_id][key][0].append(value + "之后")
                                    vars[rule_id][key][1].append(value + "及" + value + "之前")
                                elif op1 == "==":
                                    vars[rule_id][key][0].append(value)
                                    vars[rule_id][key][1].append("非" + value)
                                elif op1 == "!=":
                                    vars[rule_id][key][0].append("非" + value)
                                    vars[rule_id][key][1].append(value)
                                del cons[key]
                                del variables[key]
                            elif len(v) == 1:  # 常量
                                v = v[0]
                                if isnumber(v):
                                    value = float(v)
                                    cc = gen_cons(op1, variable, value)
                                    cons[key].append(cc)
                                    if key not in cons_detail:
                                        cons_detail[key] = []
                                    cons_detail[key].append(c)
                                else:
                                    vars[rule_id][key].append(v)
                            else:  # 未知情况
                                raise ValueError(f"未知情况！'{value}'定义在define中，是一个数组，无法处理数组")
                        else:  # 变量
                            wait_var_dic[key] = c
                            # 不用求解器，删除
                            del cons[key]
                            if key in variables:
                                del variables[key]

                elif len(value) == 4:
                    op1, value1, op2, value2 = value[:]
                    if 'sum' in value2:
                        t = value2.split('[')[0] + '[i]' + value2.split('.')[-1]  # bad
                        wait_var_dic[t] = c
                        continue
                    if key in variables:
                        variable = variables[key]
                    else:
                        variable = z3.Int(key)
                        variables[key] = variable
                        cons[key].append(variable > 0)
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
                    if op1 in ['+', '-', '*', '/', '%']:
                        v1 = gen_temp_v(op1, variable, value1)
                        cc = gen_cons(op2, v1, value2)
                    else:
                        v1 = gen_temp_v(op2, value1, value2)
                        cc = gen_cons(op1, variable, v1)
                    cons[key].append(cc)
                    if key not in cons_detail:
                        cons_detail[key] = []
                    cons_detail[key].append(c)

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
                    # if key not in cons_detail:
                    #     cons_detail[key] = []
                    # cons_detail[key].append(c)


            

        
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
        if solver.check() == z3.sat:
            rs = solver.model()
            value = int(rs[variables[variable]].as_long()) if isinstance(rs[variables[variable]], z3.IntNumRef) else float(rs[variables[variable]].as_decimal(prec=6)[:6])
            rs = [value]
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
        '''增加一次性申报特殊判定'''
        # print("操作" in vars[rule_id].keys())
        # print(vars[rule_id]['操作'])
        if "操作" in vars[rule_id].keys() and "一次性" in vars[rule_id]['操作'][0]:
            for vi,vr in enumerate(valid_value):
                valid_value[vi] = str(vr)+"(余额"+str(vr)+")"

            not_valid_value_0 = not_valid_value[0]
            for vi, vr in enumerate(not_valid_value):
                not_valid_value[vi] = str(vr) + "(余额" + str(vr) + ")"
            not_valid_value.append(str(not_valid_value_0 - 20) + "(余额" + str(not_valid_value_0 - 10) + ")")

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



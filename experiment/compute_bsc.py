import copy
import json
import re
import hanlp
import os
from ours.process_r1_to_r2 import judge_op, is_num_key, is_price_key, is_time_key
from experiment.tc import str_same

sts = hanlp.load(hanlp.pretrained.sts.STS_ELECTRA_BASE_ZH)

def judge_same(s1, s2, method="alg", threshold=0.8):
    s1, s2 = str(s1), str(s2)
    if method == "alg":
        return str_same(s1, s2, threshold)
    else:
        return sts((s1, s2)) > threshold

def is_number(s):
    try:
        s = float(s)
        return True
    except ValueError:
        return False

def compute_bsc_v1(testcases, scenarios, f):
    """
    这个函数的计算方法是，对于一条测试场景，一条用例，找用例中的每个要素在场景中是否出现了
    如果出现并且相似，认为正确，不相似认为冲突；如果没有出现，默认出现
    结果正确率偏高
    """
    # 预处理scenarios
    if_cover = [0] * len(scenarios)
    new_scenarios = []
    for scenario in scenarios:
        s = {}
        scs = scenario.split(";")
        for sc in scs:
            if "时间" not in sc:
                ss = sc.split(":")
                s[ss[0]] = ss[1]
            else:
                ss = sc.split(":")
                s[ss[0]] = ":".join(ss[1:])
        new_scenarios.append(s)
    scenarios = new_scenarios

    for testcase in testcases:
        for t in testcase:
            for iis, s in enumerate(scenarios):
                s_keys = list(s.keys())
                t_keys = list(t.keys())
                conflict = False
                find_time, find_num, find_price = False, False, False  # 匹配的数目
                # 统计s中的时间、数目、价格key
                s_time_keys = []
                for s_key in s_keys:
                    if "时间" in s_key:
                        s_time_keys.append(s_key)
                
                s_num_keys = []
                for s_key in s_keys:
                    if "数量" in s_key:
                        s_num_keys.append(s_key)
                
                s_price_keys = []
                for s_key in s_keys:
                    if "价格" in s_key or "金额" in s_key:
                        s_price_keys.append(s_key)

                for t_key in t_keys:
                    if t_key in ["rule", "测试关注点", "testid"]:
                        continue
                    if t_key == "结果":
                        # 必须相同
                        if t[t_key] != s[t_key]:
                            conflict = True
                            break
                    elif not is_time_key(t_key) and not is_num_key(t_key) and not is_price_key(t_key):
                        # 枚举约束
                        # 如果找到相同的value，就算相同
                        find = False
                        for s_key in s_keys:
                            for s_value in s[s_key].split(","):
                                if judge_same(t[t_key], s_value):
                                    find = True
                                    break
                            if find:
                                break
                        if find:
                            continue
                        # 没有找到相同的value，找是否冲突
                        if t_key not in s_keys:
                            continue
                        else:
                            conflict = True
                            break
                    elif is_time_key(t_key):
                        if len(s_time_keys) == 0:
                            conflict = True
                            break
                        find = False
                        for s_key in s_time_keys:
                            t_value = t[t_key]
                            s_value = s[s_key]
                            if ":" not in t_value and ":" not in s_value:  # 时间 is 上市首日
                                if judge_same(t_value, s_value):
                                    find = True
                                    break
                                else:
                                    continue
                            elif ":" not in t_value or ":" not in s_value:
                                continue
                            # t_value: 00:00:00-09:30:00 或 11:30:00-13:00:00 或 14:57:00-24:00:00
                            # s_value: 非9:15至11:30,13:00至15:30
                            # 将s_value、t_value格式转化
                            vs = [t.strip() for t in t_value.split("或")]
                            t_value = "{"
                            for v in vs:
                                t_value += f"[{v}],"
                            t_value = t_value[:-1] + "}"
                            fei = False
                            if "非" in s_value:
                                fei = True
                                s_value = s_value[1:]
                            vs = s_value.split(",")
                            time = []
                            for v in vs:
                                if "至" in v or "-" in v:
                                    t1 = v.split("至")[0] if "至" in v else v.split("-")[0]
                                    t2 = v.split("至")[1] if "至" in v else v.split("-")[1]
                                    if len(t1) == 4:
                                        t1 = "0" + t1 + ":00"
                                    elif len(t1) == 5:
                                        t1 = t1 + ":00"
                                    elif len(t1) == 7:
                                        t1 = "0" + t1
                                    if len(t2) == 4:
                                        t2 = "0" + t2 + ":00"
                                    elif len(t2) == 5:
                                        t2 = t2 + ":00"
                                    elif len(t2) == 7:
                                        t2 = "0" + t2
                                    time.append(t1)
                                    time.append(t2)
                                elif "前" in v or "后" in v:
                                    t = v[:-1]
                                    if len(t) == 4:
                                        t = "0" + t + ":00"
                                    elif len(t) == 5:
                                        t = t + ":00"
                                    elif len(t) == 7:
                                        t = "0" + t
                                    if "前" in v:
                                        time.append("00:00:00")
                                        time.append(t)
                                    else:
                                        time.append(t)
                                        time.append("24:00:00")
                            if fei:
                                if time[0] == "00:00:00":
                                    del time[0]
                                else:
                                    time.insert(0, "00:00:00")
                                if time[-1] == "24:00:00":
                                    del time[-1]
                                else:
                                    time.append("24:00:00")
                            s_value = "{"
                            for i in range(0, len(time), 2):
                                s_value += f"[{time[i]}-{time[i+1]}],"
                            s_value = s_value[:-1] + "}"
                            if s_value == t_value:
                                find = True
                                break
                        if find:
                            find_time = True

                    elif is_num_key(t_key):
                        if len(s_num_keys) == 0:
                            conflict = True
                            break
                        find = False
                        for s_key in s_num_keys:
                            t_value = t[t_key]
                            s_value = s[s_key]
                            if "一次性" in s_value and "(余额)" in t_value:
                                find = True
                                break
                            if "一次性" in s_value or "(余额)" in t_value:
                                continue
                            nums = [t.strip() for t in t_value.split("或")]
                            fei = False
                            if "非" in s_value:
                                s_value = s_value[1:]
                                fei = True
                            fulfill_all = True  # 这里假设满足所有约束
                            for sv in s_value.split(","):
                                fulfill = False
                                for num in nums:
                                    if num.isdigit():
                                        num = int(num)
                                    else:
                                        if judge_same(num,sv):
                                            fulfill = True
                                            break
                                        else:
                                            continue
                                    if "整数倍" in sv:
                                        value = int(re.findall(r"\d+", sv)[0])  # value的整数倍
                                        if num % value == 0 and not fei or num % value != 0 and fei:
                                            # 满足条件
                                            fulfill = True
                                            break
                                    op = judge_op(sv)
                                    value = int(re.findall(r"\d+", sv)[0])  # op value
                                    constraint_fulfill = op == ">=" and num >= value or op == "<=" and num <= value or op == ">" and num > value or op == ">" and num > value or op == "==" and num == value or op == "!=" and num != value
                                    fulfill = constraint_fulfill and not fei or not constraint_fulfill and fei
                                    if fulfill:
                                        break
                                if not fulfill:
                                    fulfill_all = False
                                    break
                            if fulfill_all:
                                find = True
                                break
                        if find:
                            find_num = True

                    else:  # "价格"/"金额" in t_key
                        if len(s_price_keys) == 0:
                            conflict = True
                            break
                        find = False
                        for s_key in s_price_keys:
                            t_value = t[t_key]
                            s_value = s[s_key]
                            prices = [t.strip() for t in t_value.split("或")]
                            fei = False
                            if "非" in s_value:
                                s_value = s_value[1:]
                                fei = True
                            fulfill_all = True  # 这里假设满足所有约束
                            for sv in s_value.split(","):
                                fulfill = False
                                for price in prices:
                                    if price.isdigit():
                                        price = float(price)
                                    else:
                                        if judge_same(price, sv):
                                            fulfill = True
                                            break
                                        else:
                                            continue
                                    op = judge_op(sv)
                                    value = float(re.findall(r"\d+", sv)[0])  # op value
                                    constraint_fulfill = op == ">=" and price >= value or op == "<=" and price <= value or op == ">" and price > value or op == ">" and price > value or op == "==" and price == value or op == "!=" and price != value
                                    fulfill = constraint_fulfill and not fei or not constraint_fulfill and fei
                                    if fulfill:
                                        break
                                if not fulfill:
                                    fulfill_all = False
                                    break
                            if fulfill_all:
                                find = True
                                break
                        if find:
                            find_price = True
                if (len(s_time_keys) == 0 or len(s_time_keys) > 0 and find_time) or (len(s_num_keys) == 0 or len(s_num_keys) > 0 and find_num) or (len(s_price_keys) == 0 or len(s_price_keys) > 0 and find_price):
                    ...
                else:
                    conflict = True
                if not conflict:
                    if_cover[iis] = 1

    for i, cover in enumerate(if_cover):
        if cover == 0:
            f.write(str(i+1))
            f.write("\n")
    return float(sum(if_cover)) / float(len(if_cover))


def compute_bsc_v2(testcases, scenarios, f, type="ours"):
    """
    这个函数的计算方法是，对于一个场景，一条用例，判断场景的每个变量在用例中是否提及（值相同），
    然后这个场景覆盖率=提及的变量数/总变量数，取最高的覆盖率
    总体的覆盖率=所有场景覆盖率的均值
    """
    # 预处理scenarios
    new_scenarios = []  # new_scenarios[i]['交易市场']='深圳证券交易所'
    scenarios_variables = []  # scenario_variables[i]['交易市场'] = 0代表该元素未被覆盖，1代表覆盖
    max_cover_varnum = [0] * len(scenarios)  # 每个测试场景的最大覆盖变量数量

    for scenario in scenarios:
        s = {}
        variables = {}
        scs = scenario.split(";")
        for sc in scs:
            if "时间" not in sc:
                ss = sc.split(":")
                s[ss[0]] = ss[1]
                variables[ss[0]] = 0
            else:
                ss = sc.split(":")
                s[ss[0]] = ":".join(ss[1:])
                variables[ss[0]] = 0
        new_scenarios.append(s)
        scenarios_variables.append(variables)
    scenarios = new_scenarios

    if type == "ours":
        testcases = [testcase for testcase_ in testcases for testcase in testcase_]

    for scenario_index, scenario in enumerate(scenarios):
        scenario_variables_total = copy.deepcopy(scenarios_variables[scenario_index])
        for testcase_index, testcase in enumerate(testcases):
            scenario_variables = copy.deepcopy(scenarios_variables[scenario_index])
            
            # 结果必须相同，否则直接算冲突
            if '结果' in scenario and '结果' in testcase and (scenario['结果'] == testcase['结果']):
                scenario_variables['结果'] = 1
            else:
                continue
            # if '结果' in scenario and '结果' in testcase and (scenario['结果'] == testcase['结果'] or scenario['结果'] == "不成功" and testcase['结果'] == "成功"):
            #     scenario_variables['结果'] = 1
            # else:
            #     continue
            
            # 计算这个testcase在scenario中覆盖了多少
            for testcase_key, testcase_value in testcase.items():
                # 无关的测试用例key跳过
                if testcase_key in ['rule', '测试关注点', 'testid', '结果']:
                    continue
                
                for scenario_key, scenario_value in scenario.items():
                    if scenario_key == "结果":
                        continue
                    # 同时为时间变量
                    if is_time_key(testcase_key) and is_time_key(scenario_key):
                        if ":" not in testcase_value and ":" not in scenario_value:  # 时间 is 上市首日 这样的，按照枚举变量处理
                            for s_value in scenario_value.split(","):
                                if judge_same(testcase_value, s_value):
                                    scenario_variables[scenario_key] = 1
                                    break
                                # else: 如果时间冲突的话，不设置对应的变量被覆盖，继续比较
                            continue
                        elif ":" not in testcase_value or ":" not in scenario_value:
                            continue
                        # else: 两个时间变量，转成相同的格式比较
                        # testcase_value: 00:00:00-09:30:00 或 11:30:00-13:00:00 或 14:57:00-24:00:00
                        # scenario_value: 非9:15至11:30,13:00至15:30
                        vs = [t.strip() for t in testcase_value.split("或")]
                        t_value = "{"
                        for v in vs:
                            t_value += f"[{v}],"
                        t_value = t_value[:-1] + "}"
                        fei = False
                        if "非" == scenario_value[0]:
                            fei = True
                            scenario_value = scenario_value[1:]
                        vs = scenario_value.split(",")
                        time = []
                        for v in vs:
                            if "至" in v or "-" in v:
                                t1 = v.split("至")[0] if "至" in v else v.split("-")[0]
                                t2 = v.split("至")[1] if "至" in v else v.split("-")[1]
                                if len(t1) == 4:
                                    t1 = "0" + t1 + ":00"
                                elif len(t1) == 5:
                                    t1 = t1 + ":00"
                                elif len(t1) == 7:
                                    t1 = "0" + t1
                                if len(t2) == 4:
                                    t2 = "0" + t2 + ":00"
                                elif len(t2) == 5:
                                    t2 = t2 + ":00"
                                elif len(t2) == 7:
                                    t2 = "0" + t2
                                time.append(t1)
                                time.append(t2)
                            elif "前" in v or "后" in v:
                                t = v[:-1]
                                if len(t) == 4:
                                    t = "0" + t + ":00"
                                elif len(t) == 5:
                                    t = t + ":00"
                                elif len(t) == 7:
                                    t = "0" + t
                                if "前" in v:
                                    time.append("00:00:00")
                                    time.append(t)
                                else:
                                    time.append(t)
                                    time.append("24:00:00")
                        if fei:
                            if time[0] == "00:00:00":
                                del time[0]
                            else:
                                time.insert(0, "00:00:00")
                            if time[-1] == "24:00:00":
                                del time[-1]
                            else:
                                time.append("24:00:00")
                        s_value = "{"
                        for i in range(0, len(time), 2):
                            s_value += f"[{time[i]}-{time[i+1]}],"
                        s_value = s_value[:-1] + "}"
                        if s_value == t_value:
                            scenario_variables[scenario_key] = 1

                    # 同时为数量变量
                    elif is_num_key(testcase_key) and is_num_key(scenario_key):
                        
                        if "一次性" in scenario_value and "(余额" in testcase_value:
                            scenario_variables[scenario_key] = 1
                            continue
                        elif "一次性" in scenario_value or "(余额)" in testcase_value:
                            continue
                        # else: 常规数值约束或枚举约束
                        nums = [t.strip() for t in testcase_value.split("或")]
                        fei = False
                        if "非" == scenario_value[0]:
                            scenario_value = scenario_value[1:]
                            fei = True
                        fulfill_all = True  # 这里假设满足所有约束
                        for sv in scenario_value.split(","):
                            fulfill = False
                            for num in nums:
                                if num.isdigit():
                                    num = int(num)
                                else:  # 枚举约束
                                    if judge_same(num, sv):
                                        fulfill = True
                                        break
                                    else:
                                        continue
                                if "整数倍" in sv:
                                    value = int(re.findall(r"\d+", sv)[0])  # value的整数倍
                                    if num % value == 0 and not fei or num % value != 0 and fei:
                                        # 满足条件
                                        fulfill = True
                                        break
                                op = judge_op(sv)
                                all_v = re.findall(f"\d+", sv)
                                if len(all_v)>0:
                                    value = float(all_v[0])  # op value
                                else:  # 场景中的价格是一个枚举变量(但price不是)
                                    continue
                                if "万" in sv:
                                    value = value * 10000
                                if "亿" in sv:
                                    value = value * 100000000
                                constraint_fulfill = op == ">=" and num >= value or op == "<=" and num <= value or op == ">" and num > value or op == "<" and num < value or op == "==" and num == value or op == "!=" and num != value
                                fulfill = constraint_fulfill and not fei or not constraint_fulfill and fei
                                if fulfill:
                                    break
                            # 如果是正例，必须fulfill_all；如果是反例，只要有一个fulfill就算成功
                            if fei and fulfill:
                                fulfill_all = True
                                break
                            if not fulfill:
                                fulfill_all = False
                                break
                        if fulfill_all:
                            scenario_variables[scenario_key] = 1

                    # 同时为价格变量
                    elif is_price_key(testcase_key) and is_price_key(scenario_key):
                        prices = [t.strip() for t in testcase_value.split("或")]
                        fei = False
                        if "非" == scenario_value[0]:
                            scenario_value = scenario_value[1:]
                            fei = True
                        fulfill_all = True  # 这里假设满足所有约束
                        for sv in scenario_value.split(","):
                            fulfill = False
                            for price in prices:
                                if is_number(price):
                                    price = float(price)
                                else:
                                    if judge_same(price, sv):
                                        fulfill = True
                                        break
                                    else:
                                        continue
                                op = judge_op(sv)
                                if op == "":
                                    op = "=="
                                all_v = re.findall(r"\d+\.\d+|\d+", sv)
                                if len(all_v)>0:
                                    value = float(all_v[0])  # op value
                                else:  # 场景中的价格是一个枚举变量(但price不是)
                                    continue
                                if "万" in sv:
                                    value = value * 10000
                                if "亿" in sv:
                                    value = value * 100000000
                                constraint_fulfill = op == ">=" and price >= value or op == "<=" and price <= value or op == ">" and price > value or op == "<" and price < value or op == "==" and price == value or op == "!=" and price != value
                                fulfill = constraint_fulfill and not fei or not constraint_fulfill and fei
                                if fulfill:
                                    break
                            if fei and fulfill:
                                fulfill_all = True
                                break
                            if not fulfill:
                                fulfill_all = False
                                break
                        if fulfill_all:
                            scenario_variables[scenario_key] = 1

                    # 同时为枚举变量
                    elif not is_time_key(testcase_key) and not is_time_key(testcase_key) and not is_num_key(testcase_key) and not is_num_key(scenario_key) and not is_price_key(testcase_key) and not is_price_key(scenario_key):
                        
                        # 对于scenario中的一条枚举变量，如果在testcase中存在value相似的字符串，则算覆盖；否则不算
                        for s_value in scenario_value.split(","):
                            if judge_same(s_value, testcase_value):
                                scenario_variables[scenario_key] = 1
                                break
            
            if "testid" in testcase:
                f.write(f"## 测试场景\"{scenario_index+1}\", 测试用例\"{testcase['testid']}\", 覆盖变量数目为{sum(scenario_variables.values())}, 未覆盖的变量包括{[key for key in scenario_variables.keys() if scenario_variables[key] == 0]}\n")
            else:
                f.write(f"## 测试场景\"{scenario_index+1}\", 测试用例\"{testcase_index}\", 覆盖变量数目为{sum(scenario_variables.values())}, 未覆盖的变量包括{[key for key in scenario_variables.keys() if scenario_variables[key] == 0]}\n")
            
            for key in scenario_variables_total.keys():
                if scenario_variables[key] == 1:
                    scenario_variables_total[key] = 1
        
        max_cover_varnum[scenario_index] = sum(scenario_variables_total.values())
        if len(scenario_variables_total.keys()) > max_cover_varnum[scenario_index]:
            f.write(f"### 测试场景\"{scenario_index+1}\", 覆盖变量的最大数目为{max_cover_varnum[scenario_index]}, 整体未覆盖的变量包括{[key for key in scenario_variables_total.keys() if scenario_variables_total[key] == 0]}\n\n")
        else:
            f.write(f"### 测试场景\"{scenario_index+1}\", 覆盖变量的最大数目为{max_cover_varnum[scenario_index]}, 所有变量全部覆盖\n\n")
    
    max_cover_rate = [max_cover_varn / len(scenarios[i]) for i, max_cover_varn in enumerate(max_cover_varnum)]
    cover_rate = sum(max_cover_rate) / len(max_cover_rate)
    return cover_rate


def compute_bsc_ours(summary_f):
    for file in sorted(os.listdir("business_scenario")):
        # if "data2" not in file:
        #     continue
        f = open(f"log/ours_{file.split('_')[0]}.log", "w", encoding="utf-8")
        testcase_file = f"rules_and_testcases_part/{file.split('_')[0]}_testcases.json"
        scenario_file = f"business_scenario/{file}"
        testcases = json.load(open(testcase_file, "r", encoding="utf-8"))
        scenarios = open(scenario_file, "r", encoding="utf-8").read().strip().split("\n")
        bsc = compute_bsc_v2(testcases, scenarios, f, type="ours")
        print(f"数据集{file.split('_')[0]}的业务场景覆盖率为{round(bsc, 4)}")
        f.write(f"数据集{file.split('_')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
        summary_f.write(f"ours在数据集{file.split('_')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
        f.close()


def compute_bsc_v3(testcases, scenarios, f):
    # 预处理scenarios
    new_scenarios = []  # new_scenarios[i]['交易市场']='深圳证券交易所'
    scenarios_variables = []  # scenario_variables[i]['交易市场'] = 0代表该元素未被覆盖，1代表覆盖
    max_cover_varnum = [0] * len(scenarios)  # 每个测试场景的最大覆盖变量数量

    for scenario in scenarios:
        s = {}
        variables = {}
        scs = scenario.split(";")
        for sc in scs:
            if "时间" not in sc:
                ss = sc.split(":")
                s[ss[0]] = ss[1]
                variables[ss[0]] = 0
            else:
                ss = sc.split(":")
                s[ss[0]] = ":".join(ss[1:])
                variables[ss[0]] = 0
        new_scenarios.append(s)
        scenarios_variables.append(variables)
    scenarios = new_scenarios

    for scenario_index, scenario in enumerate(scenarios):
        scenario_variables_total = copy.deepcopy(scenarios_variables[scenario_index])
        for testcase_index, testcase in enumerate(testcases):
            scenario_variables = copy.deepcopy(scenarios_variables[scenario_index])
            
            # 结果必须相同，否则直接算冲突
            if '结果' in scenario and '结果' in testcase and (scenario['结果'] == testcase['结果']):
                scenario_variables['结果'] = 1
            else:
                continue
            # if '结果' in scenario and '结果' in testcase and (scenario['结果'] == testcase['结果'] or scenario['结果'] == "不成功" and testcase['结果'] == "成功"):
            #     scenario_variables['结果'] = 1
            # else:
            #     continue
            
            # 计算这个testcase在scenario中覆盖了多少
            for testcase_key, testcase_value in testcase.items():
                # 无关的测试用例key跳过
                if testcase_key in ['rule', '测试关注点', 'testid', '结果'] or not isinstance(testcase_value, str):
                    continue
                
                for scenario_key, scenario_value in scenario.items():
                    if scenario_key == "结果":
                        continue
                    if judge_same(scenario_value, testcase_value):
                        scenario_variables[scenario_key] = 1
                    # 对于scenario中的一条枚举变量，如果在testcase中存在value相似的字符串，则算覆盖；否则不算
                    for s_value in scenario_value.split(","):
                        if judge_same(s_value, testcase_value):
                            scenario_variables[scenario_key] = 1
                            break
                    # 同时为时间变量
                    if scenario_variables[scenario_key] == 0 and is_time_key(testcase_key) and is_time_key(scenario_key):
                        if ":" not in testcase_value and ":" not in scenario_value:  # 时间 is 上市首日 这样的，按照枚举变量处理
                            continue
                        elif ":" not in testcase_value or ":" not in scenario_value:
                            continue
                        # else: 两个时间变量，转成相同的格式比较
                        # testcase_value: 9:15
                        # scenario_value: 非9:15至11:30,13:00至15:30
                        t_value = testcase_value.split(" ")[-1]
                        fei = False
                        if "非" == scenario_value[0]:
                            fei = True
                            scenario_value = scenario_value[1:]
                        vs = scenario_value.split(",")
                        time = []
                        for v in vs:
                            if "至" in v or "-" in v:
                                t1 = v.split("至")[0] if "至" in v else v.split("-")[0]
                                t2 = v.split("至")[1] if "至" in v else v.split("-")[1]
                                if len(t1) == 4:
                                    t1 = "0" + t1 + ":00"
                                elif len(t1) == 5:
                                    t1 = t1 + ":00"
                                elif len(t1) == 7:
                                    t1 = "0" + t1
                                if len(t2) == 4:
                                    t2 = "0" + t2 + ":00"
                                elif len(t2) == 5:
                                    t2 = t2 + ":00"
                                elif len(t2) == 7:
                                    t2 = "0" + t2
                                time.append(t1)
                                time.append(t2)
                            elif "前" in v or "后" in v:
                                t = v[:-1]
                                if len(t) == 4:
                                    t = "0" + t + ":00"
                                elif len(t) == 5:
                                    t = t + ":00"
                                elif len(t) == 7:
                                    t = "0" + t
                                if "前" in v:
                                    time.append("00:00:00")
                                    time.append(t)
                                else:
                                    time.append(t)
                                    time.append("24:00:00")
                        if fei:
                            if time[0] == "00:00:00":
                                del time[0]
                            else:
                                time.insert(0, "00:00:00")
                            if time[-1] == "24:00:00":
                                del time[-1]
                            else:
                                time.append("24:00:00")
                        for i in range(0, len(time), 2):
                            if time[i] < t_value and t_value < time[i+1]:
                                scenario_variables[scenario_key] = 1
                                break

                    # 同时为数量变量
                    elif scenario_variables[scenario_key] == 0 and is_num_key(testcase_key) and is_num_key(scenario_key):
                        
                        if "一次性" in scenario_value and "(余额" in testcase_value:
                            scenario_variables[scenario_key] = 1
                            continue
                        elif "一次性" in scenario_value or "(余额)" in testcase_value:
                            continue
                        # else: 常规数值约束
                        nums = re.findall(r"\d+", testcase_value.strip())
                        if len(nums) == 0:
                            continue
                        num = nums[0].replace(",", "")
                        fei = False
                        if "非" == scenario_value[0]:
                            scenario_value = scenario_value[1:]
                            fei = True
                        fulfill_all = True  # 这里假设满足所有约束
                        for sv in scenario_value.split(","):
                            fulfill = False
                            num = float(num)
                            if "万" in testcase_value:
                                num = num * 10000
                            if "亿" in testcase_value:
                                num = num * 100000000
                            num = int(num)
                            if "整数倍" in sv:
                                value = int(re.findall(r"\d+", sv)[0])  # value的整数倍
                                if num % value == 0 and not fei or num % value != 0 and fei:
                                    # 满足条件
                                    fulfill = True
                            else:
                                op = judge_op(sv)
                                all_v = re.findall(f"\d+", sv)
                                if len(all_v)>0:
                                    value = float(all_v[0])  # op value
                                else:  # 场景中的价格是一个枚举变量(但price不是)
                                    continue
                                if "万" in sv:
                                    value = value * 10000
                                if "亿" in sv:
                                    value = value * 100000000
                                constraint_fulfill = op == ">=" and num >= value or op == "<=" and num <= value or op == ">" and num > value or op == "<" and num < value or op == "==" and num == value or op == "!=" and num != value
                                fulfill = constraint_fulfill and not fei or not constraint_fulfill and fei

                            # 如果是正例，必须fulfill all；如果是反例，只要有一个fulfill就算成功
                            if fei and fulfill:
                                fulfill_all = True
                                break
                            if not fulfill:
                                fulfill_all = False
                                break
                        if fulfill_all:
                            scenario_variables[scenario_key] = 1

                    # 同时为价格变量
                    elif scenario_variables[scenario_key] == 0 and is_price_key(testcase_key) and is_price_key(scenario_key):
                        
                        prices = re.findall(r"\d+\.\d+|\d+", testcase_value.strip())
                        if len(prices) == 0:
                            continue
                        price = prices[0].replace(",", "")
                        fei = False
                        if "非" == scenario_value[0]:
                            scenario_value = scenario_value[1:]
                            fei = True
                        fulfill_all = True  # 这里假设满足所有约束
                        for sv in scenario_value.split(","):
                            fulfill = False

                            price = float(price)
                            if "万" in scenario_value:
                                price = price * 10000
                            if "亿" in scenario_value:
                                price = price * 100000000
                            op = judge_op(sv)
                            all_v = re.findall(f"\d+", sv)
                            if len(all_v)>0:
                                value = float(all_v[0])  # op value
                            else:  # 场景中的价格是一个枚举变量(但price不是)
                                continue
                            if "万" in sv:
                                value = value * 10000
                            if "亿" in sv:
                                value = value * 100000000
                            constraint_fulfill = op == ">=" and price >= value or op == "<=" and price <= value or op == ">" and price > value or op == "<" and price < value or op == "==" and price == value or op == "!=" and price != value
                            fulfill = constraint_fulfill and not fei or not constraint_fulfill and fei
                            
                            if fei and fulfill:
                                fulfill_all = True
                                break
                            if not fulfill:
                                fulfill_all = False
                                break
                        if fulfill_all:
                            scenario_variables[scenario_key] = 1

            if "testid" in testcase:
                f.write(f"## 测试场景\"{scenario_index+1}\", 测试用例\"{testcase['testid']}\", 覆盖变量数目为{sum(scenario_variables.values())}, 未覆盖的变量包括{[key for key in scenario_variables.keys() if scenario_variables[key] == 0]}\n")
            else:
                f.write(f"## 测试场景\"{scenario_index+1}\", 测试用例\"{testcase_index}\", 覆盖变量数目为{sum(scenario_variables.values())}, 未覆盖的变量包括{[key for key in scenario_variables.keys() if scenario_variables[key] == 0]}\n")
            
            for key in scenario_variables_total.keys():
                if scenario_variables[key] == 1:
                    scenario_variables_total[key] = 1
        
        max_cover_varnum[scenario_index] = sum(scenario_variables_total.values())
        if len(scenario_variables_total.keys()) > max_cover_varnum[scenario_index]:
            f.write(f"### 测试场景\"{scenario_index+1}\", 覆盖变量的最大数目为{max_cover_varnum[scenario_index]}, 整体未覆盖的变量包括{[key for key in scenario_variables_total.keys() if scenario_variables_total[key] == 0]}\n\n")
        else:
            f.write(f"### 测试场景\"{scenario_index+1}\", 覆盖变量的最大数目为{max_cover_varnum[scenario_index]}, 所有变量全部覆盖\n\n")
    
    max_cover_rate = [max_cover_varn / len(scenarios[i]) for i, max_cover_varn in enumerate(max_cover_varnum)]
    cover_rate = sum(max_cover_rate) / len(max_cover_rate)
    return cover_rate

def compute_bsc_llm(summary_f):
    for file in sorted(os.listdir("llm_result")):
        if "testcase" in file:
            llm = file.split("_")[0]
            f = open(f"log/{llm}_{file.split('_')[-1].split('.')[0]}.log", "w", encoding="utf-8")
            testcase_file = "llm_result/" + file
            scenario_file = f"business_scenario/{file.split('_')[-1].split('.')[0]}_scenario.txt"
            testcases = json.load(open(testcase_file, "r", encoding="utf-8"))
            scenarios = open(scenario_file, "r", encoding="utf-8").read().strip().split("\n")
            bsc = compute_bsc_v2(testcases, scenarios, f, type="llm")
            print(f"{llm}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}")
            f.write(f"{llm}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
            summary_f.write(f"{llm}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
            f.close()

def compute_bsc_non_expert(summary_f):
    bsc_list = []
    for file in sorted(os.listdir("non_expert_result")):
        if ".json" in file:
            testcases = json.load(open(f"non_expert_result/{file}", "r", encoding="utf-8"))
            dataset = file.split(".")[0].split("_")[-1]
            scenarios = open(f"business_scenario/{dataset}_scenario.txt", "r", encoding="utf-8").read().strip().split("\n")
            f = open(f"log/{file.split('.')[0]}.log", "w", encoding="utf-8")
            bsc = compute_bsc_v2(testcases, scenarios, f, type="human")
            bsc_list.append(bsc)
            human = "_".join(file.split("_")[:2])
            print(f"{human}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}")
            f.write(f"{human}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
            summary_f.write(f"{human}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
            f.close()
    # 计算均值
    for dataset in range(5):
        bsc_sum = 0.0
        for i in range(dataset, len(bsc_list), 5):
            bsc_sum += bsc_list[i]
        bsc_avg = bsc_sum / 4.0
        print(f"non-expert在数据集{dataset+1}的平均业务场景覆盖率为{round(bsc_avg, 4)}")
        summary_f.write(f"non-expert在数据集{dataset+1}的平均业务场景覆盖率为{round(bsc_avg, 4)}\n")


def compute_bsc_expert(summary_f):
    for file in sorted(os.listdir("expert_result")):
        if ".json" in file:
            testcases = json.load(open(f"expert_result/{file}", "r", encoding="utf-8"))
            dataset = file.split(".")[0].split("_")[-1]
            scenarios = open(f"business_scenario/{dataset}_scenario.txt", "r", encoding="utf-8").read().strip().split("\n")
            f = open(f"log/{file.split('.')[0]}.log", "w", encoding="utf-8")
            # bsc = compute_bsc_v2(testcases, scenarios, f, type="human")
            bsc = compute_bsc_v3(testcases, scenarios, f)
            human = "_".join(file.split("_")[:2])
            print(f"{human}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}")
            f.write(f"{human}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
            summary_f.write(f"{human}在数据集{file.split('_')[-1].split('.')[0]}的业务场景覆盖率为{round(bsc, 4)}\n")
            f.close()


if __name__ == "__main__":
    summary_f = open("log/bsc.log", "w", encoding="utf-8")
    compute_bsc_ours(summary_f)
    # compute_bsc_llm(summary_f)
    # compute_bsc_non_expert(summary_f)
    # compute_bsc_expert(summary_f)
    summary_f.close()
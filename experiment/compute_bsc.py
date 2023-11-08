import json
import re

from ours.process_r1_to_r2 import judge_op

def compute_bsc(testcases, scenarios, f):
    # 处理scenarios
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
                have_time, have_num, have_price = False, False, False
                find_time, find_num, find_price = False, False, False
                for t_key in t_keys:
                    if t_key in ["rule", "测试关注点", "testid"]:
                        continue
                    if "时间" not in t_key and "数量" not in t_key and "价格" not in t_key and "金额" not in t_key:
                        # 枚举约束
                        # 如果找到相同的value，就算相同
                        find = False
                        for s_key in s_keys:
                            if t[t_key] in s[s_key].split(","):
                                find = True
                                break
                        if find:
                            continue
                        # 没有找到相同的value，找是否冲突
                        if t_key not in s_keys:
                            continue
                        else:
                            conflict = True
                            break
                    elif "时间" in t_key:
                        s_time_keys = []
                        for s_key in s_keys:
                            if "时间" in s_key:
                                s_time_keys.append(s_key)
                        if len(s_time_keys) == 0:
                            conflict = True
                            break
                        have_time = True
                        find = False
                        for s_key in s_time_keys:
                            t_value = t[t_key]
                            s_value = s[s_key]
                            # t_value: '00:00:00-09:30:00' 或 '11:30:00-13:00:00' 或 '14:57:00-24:00:00'
                            # s_value: 非9:15至11:30,13:00至15:30
                            # 将s_value、t_value格式转化
                            vs = [t.strip()[1:-1] for t in t_value.split("或")]
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

                    elif "数量" in t_key:
                        s_num_keys = []
                        for s_key in s_keys:
                            if "数量" in s_key:
                                s_num_keys.append(s_key)
                        if len(s_num_keys) == 0:
                            conflict = True
                            break
                        have_num = True
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
                                    num = int(num)
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
                        s_price_keys = []
                        for s_key in s_keys:
                            if "价格" in s_key or "金额" in s_key:
                                s_price_keys.append(s_key)
                        if len(s_price_keys) == 0:
                            conflict = True
                            break
                        find = False
                        have_price = False
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
                                        if price in sv:
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
                if (not have_num or have_num and find_num) or (not have_price or have_price and find_price) or (not have_time or have_time and find_time):
                    ...
                else:
                    conflict = True
                if not conflict:
                    if_cover[iis] = 1

    for i, cover in enumerate(if_cover):
        if cover == 0:
            f.write(str(i))
            f.write("\n")
    return float(sum(if_cover)) / float(len(if_cover))


if __name__ == "__main__":
    testcase_file = "rules_and_testcases_part/data3_testcases.json"
    scenario_file = "business_scenario/data3_scenario.txt"
    testcases = json.load(open(testcase_file, "r", encoding="utf-8"))
    scenarios = open(scenario_file, "r", encoding="utf-8").read().strip().split("\n")
    f = open("bsc.log", "w", encoding="utf-8")
    bsc = compute_bsc(testcases, scenarios, f)
    f.close()
    print(f"文件{testcase_file.split('_')[0]}的业务场景覆盖率为{round(bsc, 4)}")
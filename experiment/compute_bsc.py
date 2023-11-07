import json

def compute_bsc(testcases, scenarios):
    # 处理scenarios
    if_cover = [0] * len(scenarios)
    new_scenarios = []
    for scenario in scenarios:
        s = {}
        scs = scenario.split(";")
        for sc in scs:
            ss = sc.split(":")
            s[ss[0]] = ss[1]
        new_scenarios.append(s)
    scenarios = new_scenarios

    for testcase in testcases:
        for t in testcase:
            for i, s in enumerate(scenarios):
                s_keys = list(s.keys())
                t_keys = list(t.keys())
                conflict = False
                for t_key in t_keys:
                    if "时间" not in t_key and "数量" not in t_key and "价格" not in t_key:
                        # 枚举约束
                        if t_key not in s_keys:
                            continue
                        else:
                            if t[t_key] not in s[t_key]:
                                conflict = True
                                break
                    elif "时间" in t_key:
                        t_value = t[t_key]
                        
                    elif "数量" in t_key:
                        ...
                    else:  # "价格" in t_key
                        ...
                if not conflict:
                    if_cover[i] = 1

    return float(sum(if_cover)) / float(len(if_cover))


if __name__ == "__main__":
    testcase_file = "rules_and_testcases_part/data3_testcases.json"
    scenario_file = "business_scenario/data3_scenario.txt"
    testcases = json.load(open(testcase_file, "r", encoding="utf-8"))
    scenarios = open(scenario_file, "r", encoding="utf-8").read().strip().split("\n")
    bsc = compute_bsc(testcases, scenarios)
    print(f"文件{testcase_file.split('_')[0]}的业务场景覆盖率为{round(bsc, 4)}")
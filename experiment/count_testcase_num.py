import json
import os

def count_testcase_num(data):
    if len(data) > 0:
        if isinstance(data[0], list):
            data = [di for d in data for di in d]
    return len(data)

if __name__ == "__main__":
    f = open("log/testcase_num.log", "w", encoding="utf-8")
    for file in sorted(os.listdir("expert_result")):
        if ".json" in file:
            data = json.load(open("expert_result/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            f.write(f"文件{file}测试用例数目: {num}\n")
    for file in sorted(os.listdir("non_expert_result")):
        if ".json" in file:
            data = json.load(open("non_expert_result/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            f.write(f"文件{file}测试用例数目: {num}\n")
    for file in sorted(os.listdir("llm_result"), key=lambda x: "a_" + x if "chatgpt" in x else "b_" + x):
        if ".json" in file:
            data = json.load(open("llm_result/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            f.write(f"文件{file}测试用例数目: {num}\n")
    for file in sorted(os.listdir("rules_and_testcases_for_experiment")):
        if ".json" in file:
            data = json.load(open("rules_and_testcases_for_experiment/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            f.write(f"文件{file}测试用例数目: {num}\n")
    f.close()
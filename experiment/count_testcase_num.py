import json
import os

def count_testcase_num(data):
    if len(data) > 0:
        if isinstance(data[0], list):
            data = [di for d in data for di in d]
    return len(data)

if __name__ == "__main__":
    for file in sorted(os.listdir("expert_result")):
        if ".json" in file:
            data = json.load(open("expert_result/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            print(f"文件{file}测试用例数目: {num}")
    for file in sorted(os.listdir("non_expert_result")):
        if ".json" in file:
            data = json.load(open("non_expert_result/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            print(f"文件{file}测试用例数目: {num}")
    for file in sorted(os.listdir("llm_result")):
        if ".json" in file:
            data = json.load(open("llm_result/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            print(f"文件{file}测试用例数目: {num}")
    for file in sorted(os.listdir("rules_and_testcases_part")):
        if ".json" in file:
            data = json.load(open("rules_and_testcases_part/" + file, "r", encoding="utf-8"))
            num = count_testcase_num(data)
            print(f"文件{file}测试用例数目: {num}")
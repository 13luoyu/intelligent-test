import json
import os


def non_expert_result_to_testcase(s):
    lines = [line.strip() for line in s.split("\n")]
    testcases = []
    casestr = ""
    begin, end = False, False
    for line in lines:
        if line == "":
            continue
        if "{" in line:
            casestr += line[line.find("{"):]
            begin = True
        if "}" in line:
            if "{" not in line:
                casestr += line[:line.rfind("}")+1]
            else:
                casestr = casestr[:casestr.rfind("}")+1]
            end = True
        if "{" not in line and "}" not in line and begin:
            casestr += line
        if end:
            casestr = casestr.replace("，", ",").replace("\t", "").replace(" ", "")
            if casestr[-2] == ",":
                casestr = casestr[:-2] + "}"
            if casestr.count("{") > 1:
                casestr = casestr.replace("}{", "},{")
                testcase = json.loads(f"[{casestr}]")
                testcases += testcase
            else:
                testcase = json.loads(casestr)
                testcases.append(testcase)
            end = False
            begin = False
            casestr = ""
    return testcases


if __name__ == "__main__":
    for file in os.listdir("non_expert_result"):
        if ".txt" in file:
            print(f"处理文件{file}")
            with open("non_expert_result/" + file, "r", encoding="utf-8") as f:
                s = f.read()
            ss = s.split("数据集")
            for i in range(5):
                testcases = non_expert_result_to_testcase(ss[i+1])
                json.dump(testcases, open(f"non_expert_result/{file[:-4]}_data{i+1}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
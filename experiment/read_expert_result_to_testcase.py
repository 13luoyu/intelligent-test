import json
import os

def expert_result_to_testcase(s):
    s = s.replace("：", ":")
    lines = [si.strip() for si in s.split("\n")]
    casestr = ""
    testcases = []
    begin = False
    for line in lines:
        if line == "":
            continue
        if line == "{":
            casestr += line
            begin = True
        if line == "}":
            casestr = casestr[:-1] + line
            print(casestr)
            testcases.append(json.loads(casestr))
            casestr = ""
            begin = False
        if line != "{" and line != "}" and begin:
            ss = line.split(":")
            ss = [ss[0], ":".join(ss[1:])]
            for i, si in enumerate(ss):
                if si[0] != "\"":
                    ss[i] = "\"" + si
                if si[-1] != "\"":
                    ss[i] = ss[i] + "\""
            casestr += ":".join(ss) + ","
    return testcases

if __name__ == "__main__":
    for file in os.listdir("expert_result"):
        if "expert" in file and ".txt" in file:
            print(f"处理{file}")
            s = open(f"expert_result/{file}", "r", encoding="utf-8").read()
            testcases = expert_result_to_testcase(s)
            json.dump(testcases, open(f"expert_result/{file.split('.')[0]}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
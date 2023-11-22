import os
import json

def real_llmchat_to_testcase(s):
    lines = s.split("\n")
    testcases = []
    casestr = ""
    A_num = 0
    begin = False
    for line in lines:
        line = line.strip()
        if line == "":
            continue
        if "A" == line:
            A_num += 1
        if A_num <= 1:
            continue
        end = False
        if line[0] == "{":
            casestr += line
            begin = True
            if line[-1] == "}":
                end = True
            elif line[-2:] == "},":
                casestr = casestr[:-1]
                end = True
        elif line[-1] == "}":
            casestr += line
            end = True
        elif line[-2:] == "},":
            casestr += line[:-1]
            end = True
        elif begin:
            casestr += line
        if end:
            begin = False
            casestr = casestr.replace("，", ",")
            # print(casestr)
            if casestr.count("{") > 1:
                testcase = json.loads(f"[{casestr}]")
                testcases += testcase
            else:
                testcase = json.loads(casestr)
                testcases.append(testcase)
            casestr = ""
    return testcases


if __name__ == "__main__":
    for file in os.listdir("llm_result/"):
        if "_chat_" in file:
            print("处理文件" + file)
            llm = file.split("_")[0]
            dataset = file.split("_")[-1].split(".")[0]
            with open("llm_result/" + file, "r", encoding="utf-8") as f:
                s = f.read()
            testcases = real_llmchat_to_testcase(s)
            json.dump(testcases, open(f"llm_result/{llm}_testcase_{dataset}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
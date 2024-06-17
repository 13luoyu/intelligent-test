# 检查标好数据的json文件是否正确

import json
import os

# 检查text和label的长度是否相同
def check_tc_data_length(file):
    rules = json.load(open(file, "r", encoding="utf-8"))
    for rule in rules:
        text_length = len(rule["text"])
        label_length = len(rule["label"].split(" "))
        if text_length != label_length:
            print(file)
            print(text_length, label_length)
            print(f"{rule['text']}\n")
    # print(f"{file} Done!")


def check_assemble_annotation(datas):
    for data in datas:
        answer = data["answer"]
        answer = answer.split("\n")
        count = 1
        for i, a in enumerate(answer):
            if i % 3 == 0:
                if f"rule {count}" != a and "or relation" not in a:
                    print(data,a)
                    exit(0)
                count += 1
            elif i % 3 == 1:
                cnts = a.split(" ")
                c = 0
                while c < len(cnts):
                    if c == 0:
                        if cnts[c] != "if":
                            print(1,data,a)
                            exit(0)
                    elif (c-1) % 4 == 3:
                        if cnts[c] != "and":
                            print(2,data,a)
                            exit(0)
                    c += 1
            elif i % 3 == 2:
                cnts = a.split(" ")
                c = 0
                while c < len(cnts):
                    if c == 0:
                        if cnts[c] != "then":
                            print(3,data,a)
                            exit(0)
                    elif (c-1) % 4 == 3:
                        if cnts[c] != "and":
                            print(4,data,a)
                            exit(0)
                    c += 1


if __name__ == "__main__":
    print("### Check data_for_LLM_v1 start!")
    check_tc_data_length("../data/data_for_LLM_v1/rules.json")
    for file in os.listdir("../data/data_for_LLM_v1/business_rules/json_for_token_classification/"):
        if "finish" in file:
            check_tc_data_length("../data/data_for_LLM_v1/business_rules/json_for_token_classification/" + file)
    
    for file in os.listdir("../data/data_for_LLM_v1/"):
        if "tc" in file and ".json" in file:
            check_tc_data_length("../data/data_for_LLM_v1/" + file)
    print("### Check data_for_LLM_v1 Done!")

    print("### Check data_for_LLM_v2 start!")
    check_assemble_annotation(json.load(open("../data/data_for_LLM_v2/assemble_annotation_v2.json", "r", encoding="utf-8")))
    print("### Check data_for_LLM_v2 Done!")
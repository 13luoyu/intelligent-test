import json
import os

# 统计文件中有多少条数据，其中有多少条规则，多少条领域知识，多少无法测试的语言
def count(dir):
    total_num  = 0
    rule_num, knowledge_num, other_num = 0, 0, 0
    for file in os.listdir(dir):
        if "finish" not in file:
            continue
        rules = json.load(open(dir + file, "r", encoding="utf-8"))
        total_num += len(rules)
        for rule in rules:
            if rule["type"] == "0":
                other_num += 1
            elif rule["type"] == "1":
                rule_num += 1
            elif rule["type"] == "2":
                knowledge_num += 1
    print(f"总共数据量：{total_num}, 其中有规则{rule_num}条，知识{knowledge_num}条，其他{other_num}条")


# count("../data/业务规则/json_for_sequence_classification/")

def count_file(file):
    print(len(json.load(open(file, "r", encoding="utf-8"))))

count_file("../data/sc_train_data_full.json")
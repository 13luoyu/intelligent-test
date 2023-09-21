import json
import os

# 统计目录下有多少条数据，其中有多少条规则，多少条领域知识，多少无法测试的语言
def count_dir(dir):
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

# 统计文件中的规则数
def count2(file):
    rules = json.load(open(file, "r", encoding="utf-8"))
    x = 0
    for rule in rules:
        if rule["type"] == "1":
            x += 1
    print(f"总共：{len(rules)}，规则：{x}")

# 统计json文件的数据个数
def count_file(file):
    print(len(json.load(open(file, "r", encoding="utf-8"))))



if __name__ == "__main__":
    count_dir("../data/业务规则/json_for_sequence_classification/")
    count_file("../data/sc_train_data_full.json")  # 训练数据量
    count_file("../data/sc_validate_data.json")  # 验证数据量
    count_file("../data/tc_train_data_all_full.json")  # 训练数据量
    count_file("../data/tc_validate_data_all.json")  # 验证数据量
    count_file("../data/rules.json")  # 总计规则数
    count_file("../data/knowledge.json")  # 总计知识数
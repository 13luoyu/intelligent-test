import os
import json
import random
import copy

# 将所有的数据按照9：1分成训练集和测试集
def integrate_dir(in_dir: str, train_file: str, validate_file: str):
    all_rules = []
    for file in os.listdir(in_dir):
        if "finish" in file:
            rules = json.load(open(in_dir + file, "r", encoding="utf-8"))
            all_rules += rules
    random.shuffle(all_rules)
    rule_num = len(all_rules)
    train_data, validate_data = all_rules[:int(rule_num/10*9)], all_rules[int(rule_num/10*9):]
    if "sequence" in in_dir:
        print(f"划分规则筛选数据：训练集有数据{len(train_data)}条，验证集有数据{len(validate_data)}条。")
    else:
        print(f"划分信息抽取数据：训练集有数据{len(train_data)}条，验证集有数据{len(validate_data)}条。")
    json.dump(train_data, open(train_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(validate_data, open(validate_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


def integrate_file(in_file: str, train_file: str, validate_file: str):
    all_rules = json.load(open(in_file, "r", encoding="utf-8"))
    random.shuffle(all_rules)
    rule_num = len(all_rules)
    train_data, validate_data = all_rules[:int(rule_num/10*9)], all_rules[int(rule_num/10*9):]
    print(f"划分所有规则的信息抽取数据：训练集有数据{len(train_data)}条，验证集有数据{len(validate_data)}条。")
    json.dump(train_data, open(train_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(validate_data, open(validate_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


# 挑选所有的规则，并赋予它们标签
def select_rule(seq_dir: str, tok_dir: str, rule_file: str):
    rules = []
    for file in os.listdir(seq_dir):
        if "finish" not in file:
            continue
        local_rules = []
        datas = json.load(open(seq_dir + file, "r", encoding="utf-8"))
        for data in datas:
            if data["type"] == "1":
                local_rules.append(data)
        if file not in os.listdir(tok_dir):
            continue
        datas = json.load(open(tok_dir + file, "r", encoding="utf-8"))
        data_len = len(datas)
        i = 0
        for j, rule in enumerate(local_rules):
            if i >= data_len:
                i = 0
            begin_index = datas[i]["text"].find(rule["text"])
            restart = False  # 有些规则如果没有标注的话，即遍历两边还没有发现，就不考虑了
            while begin_index == -1:
                i += 1
                if i >= data_len:
                    if not restart:
                        restart = True
                        i = 0
                    else:
                        i = 0
                        break
                begin_index = datas[i]["text"].find(rule["text"])
            if begin_index != -1:
                rule["label"] = " ".join(datas[i]["label"].split(" ")[begin_index:begin_index + len(rule["text"])])
        rules += [local_rule for local_rule in local_rules if local_rule["label"] != ""]
    json.dump(rules, open(rule_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


def integrate_all(sc_in_dir: str, sc_out_file: str, tc_in_dir: str, tc_out_file: str):
    all = []
    for file in os.listdir(sc_in_dir):
        if "finish" in file:
            data = json.load(open(sc_in_dir + file, "r", encoding="utf-8"))
            all += data
    json.dump(all, open(sc_out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    all = []
    for file in os.listdir(tc_in_dir):
        if "finish" in file:
            data = json.load(open(tc_in_dir + file, "r", encoding="utf-8"))
            all += data
    json.dump(all, open(tc_out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


if __name__ == "__main__":
    # 将句分类标注好的数据9：1分到对应文件
    integrate_dir("../data/business_rules/annotation_for_sequence_classification/", "../data/data_for_LLM_encoder/sc_train_data.json", "../data/data_for_LLM_encoder/sc_validate_data.json")
    # 将字分类标注好的数据9：1分到对应文件
    integrate_dir("../data/business_rules/annotation_for_token_classification/", "../data/data_for_LLM_encoder/tc_train_data.json", "../data/data_for_LLM_encoder/tc_validate_data.json")
    # 挑选所有的规则，并赋予它们每个字的标签，生成rules.json
    select_rule("../data/business_rules/annotation_for_sequence_classification/", "../data/business_rules/annotation_for_token_classification/", "../data/data_for_LLM_encoder/rules.json")
    # 将rules.json9：1分到对应文件
    integrate_file("../data/data_for_LLM_encoder/rules.json", "../data/data_for_LLM_encoder/tc_train_data_rules.json", "../data/data_for_LLM_encoder/tc_validate_data_rules.json")
    # 将所有字分类、句分类数据整合在一起
    integrate_all("../data/business_rules/annotation_for_sequence_classification/", "../data/data_for_LLM_encoder/sc_data.json", "../data/business_rules/annotation_for_token_classification/", "../data/data_for_LLM_encoder/tc_data.json")

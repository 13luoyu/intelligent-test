import os
import json
import random

def integrate(in_dir: str, train_file: str, validate_file: str):
    all_rules = []
    for file in os.listdir(in_dir):
        if "finish" in file:
            rules = json.load(open(in_dir + file, "r", encoding="utf-8"))
            all_rules += rules
    random.shuffle(all_rules)
    rule_num = len(all_rules)
    train_data, validate_data = all_rules[:int(rule_num/10*9)], all_rules[int(rule_num/10*9):]
    print(f"训练集有数据{len(train_data)}条，验证集有数据{len(validate_data)}条。")
    json.dump(train_data, open(train_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(validate_data, open(validate_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


if __name__ == "__main__":
    integrate("../data/业务规则/json_for_sequence_classification/", "../data/sc_train_data.json", "../data/sc_validate_data.json")
    integrate("../data/业务规则/json_for_token_classification/", "../data/tc_data_train_data.json", "../data/tc_validate_data.json")
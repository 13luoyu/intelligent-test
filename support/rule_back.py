import json
import os

# 将rules中的标注写到对应的标注文件中

def rule_back(tok_dir: str, rule_file: str):
    rules = json.load(open(rule_file, "r", encoding="utf-8"))
    for file in os.listdir(tok_dir):
        if "finish" not in file:
            continue
        datas = json.load(open(tok_dir + file, "r", encoding="utf-8"))
        for rule in rules:
            for data in datas:
                begin_index = data["text"].find(rule["text"])
                if begin_index != -1:
                    data_label = data["label"].split(" ")
                    data_label[begin_index:begin_index + len(rule["text"])] = rule["label"].split(" ")
                    data["label"] = " ".join(data_label)
        json.dump(datas, open(tok_dir + file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    


rule_back("../data/业务规则/json_for_token_classification/", "../data/rules.json")
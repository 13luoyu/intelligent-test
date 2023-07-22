import json
import os

# 将rules中的标注写到对应的标注文件中

def select_rule(tok_dir: str, rule_file: str):
    rules = json.load(open(rule_file, "r", encoding="utf-8"))
    for rule in rules:
        for file in os.listdir(tok_dir):
            if "finish" not in file:
                continue
            datas = json.load(open(tok_dir + file, "r", encoding="utf-8"))
            for data in datas:
                begin_index = data["text"].find(rule["text"])
                if begin_index != -1:
                    data["label"][begin_index:begin_index + len(rule["text"])] = rule["label"]
            json.dump(datas, open(tok_dir + file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
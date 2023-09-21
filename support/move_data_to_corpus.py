import json
import os

# 将data目录下标注好的数据分别复制到coprus目录下

for file in os.listdir("../data/业务规则/json_for_sequence_classification/"):
    if "finish" in file:
        rules = json.load(open("../data/业务规则/json_for_sequence_classification/" + file, "r", encoding="utf-8"))
        json.dump(rules, open(f"../corpus/rule_filtering/{file[7:]}", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

for file in os.listdir("../data/业务规则/json_for_token_classification/"):
    if "finish" in file:
        rules = json.load(open("../data/业务规则/json_for_token_classification/" + file, "r", encoding="utf-8"))
        json.dump(rules, open(f"../corpus/rule_element_extraction/{file[7:]}", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
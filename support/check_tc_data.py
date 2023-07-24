# 检查标好数据的json文件是否正确

import json
import os

# 检查text和label的长度是否相同
def check_length(file):
    rules = json.load(open(file, "r", encoding="utf-8"))
    for rule in rules:
        text_length = len(rule["text"])
        label_length = len(rule["label"].split(" "))
        if text_length != label_length:
            print(file)
            print(text_length, label_length)
            print(f"{rule['text']}\n")
    print("Done!")


if __name__ == "__main__":
    check_length("../data/rules.json")
    for file in os.listdir("../data/业务规则/json_for_token_classification/"):
        if "finish" in file:
            check_length("../data/业务规则/json_for_token_classification/" + file)
    
    for file in os.listdir("../data/"):
        if "tc" in file and ".json" in file:
            check_length("../data/" + file)
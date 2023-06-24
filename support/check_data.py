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
            print(text_length, label_length)
            print(f"{rule['text']}\n")
    print("Done!")


if __name__ == "__main__":
    check_length("../data/tc_train_data_full.json")
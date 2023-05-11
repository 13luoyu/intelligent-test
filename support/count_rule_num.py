import json

# 输出一个json规则文件中有多少条规则

def count(file):
    rules = json.load(open(file, "r", encoding="utf-8"))
    print(len(rules))


count("../data/深交所业务规则/json/finished_v3_深圳证券交易所债券交易规则.json")
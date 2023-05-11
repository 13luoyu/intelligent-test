# token classification任务

import json

def token_classification_with_algorithm(rule, knowledge):
    # For Show
    if rule["id"] == "3.1.5":
        rule["label"] = "O O O O O O O O O O O O O O O O O O O O B-交易品种 I-交易品种 O O O O O O O O O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O"
    elif rule["id"] == "3.3.4":
        rule["label"] = "O O O O O O O O O B-交易品种 I-交易品种 O O O O O O O O O O O O O O O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-交易品种 I-交易品种 I-交易品种 I-交易品种 O B-key I-key I-key I-key O O O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O B-操作 I-操作 O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O B-操作 I-操作 I-操作 I-操作 I-操作 O B-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 O B-key I-key I-key I-key O O O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-key I-key I-key I-key O O O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-key I-key I-key I-key O O B-op I-op I-op B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-交易品种 I-交易品种 I-交易品种 I-交易品种 B-key I-key I-key I-key O O B-op I-op I-op B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O B-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 B-key I-key I-key I-key O O O B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O O O O B-交易品种 I-交易品种 O O O B-key I-key I-key I-key I-key I-key I-key I-key B-op I-op I-op I-op B-数量 I-数量 I-数量 I-数量 I-数量 I-数量 I-数量 O"
    elif rule["id"] == "3.3.6":
        rule["label"] = "O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-交易品种 I-交易品种 I-交易品种 I-交易品种 O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O B-价格 I-价格 I-价格 I-价格 I-价格 I-价格 O B-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 I-交易品种 O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O B-价格 I-价格 I-价格 I-价格 I-价格 I-价格 O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 I-交易方式 I-交易方式 O O B-交易品种 I-交易品种 O O O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O B-价格 I-价格 I-价格 I-价格 I-价格 I-价格 I-价格 O"
    elif rule["id"] == "3.3.10":
        rule["label"] = "O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-操作人 I-操作人 I-操作人 I-操作人 I-操作人 O B-value I-value I-value I-value O O B-操作 I-操作 O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-操作人 I-操作人 I-操作人 I-操作人 I-操作人 O B-value I-value I-value I-value O O B-操作 I-操作 O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 I-交易方式 I-交易方式 O O B-操作人 I-操作人 I-操作人 I-操作人 I-操作人 O O O O O B-value I-value B-or I-or B-value I-value I-value I-value O O B-操作 I-操作 O"

def token_classification_with_model_and_algorithm(rule, model_path, knowledge):
    ...

def token_classification(in_file: str, out_file: str, knowledge_file: str, mode: int = 0):
    tci = json.load(open(in_file, "r", encoding="utf-8"))
    tco = []
    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    if mode == 0:
        for rule in tci:
            token_classification_with_algorithm(rule, knowledge)
        json.dump(tci, open(out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    elif mode == 1:
        ...
    else:
        raise ValueError(f"mode应该设置为0或1，不支持的值：mode = {mode}")


if __name__ == "__main__":
    token_classification("rules_cache/tci.json", "rules_cache/tco.json", "../data/knowledge.json")
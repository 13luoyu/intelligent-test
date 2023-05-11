# sequence classification任务
import json

def sequence_classification(in_file: str, out_file: str, mode: int = 0):
    sci = json.load(open(in_file, "r", encoding="utf-8"))
    if mode == 0:
        for rule in sci:
            sentence = rule["text"]
            # 是时间、数量、价格等要求
            if "元" in sentence or "匿名方式" in sentence or ":" in sentence:
                rule["type"] = "1"
            else:
                rule["type"] = "0"
        json.dump(sci, open(out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    elif mode == 1:
        ...
    else:
        raise ValueError(f"mode应该设置为0或1，不支持的值：mode = {mode}")


if __name__ == "__main__":
    sequence_classification("rules_cache/sci.json", "rules_cache/sco.json")
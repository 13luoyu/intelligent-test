import json

# 将sequence classification output的结果组合成token classification input的格式

def sco_to_tci(sco_file: str, tci_file: str):
    sco = json.load(open(sco_file, "r", encoding="utf-8"))
    last_id = ""
    text = ""
    tci = []
    t = {}
    for rule in sco:
        rule["id"] = rule["id"][:-2]
        # 如果id相同且不为""
        if rule["id"] == last_id and last_id != "":
            # 如果type="1"，合并
            if rule["type"] == "1":
                text += rule["text"]
            # 否则忽略本规则
        # 如果id不同，且上面已经是一条语句了
        elif rule["id"] != last_id and last_id != "":
            # 可测试的规则
            if text != "":
                t["id"] = last_id
                t["text"] = text
                t["label"] = ""
                tci.append(t)
                t = {}
                text = ""
            last_id = rule["id"]
            if rule["type"] == "1":
                text += rule["text"]
        elif rule["id"] != last_id and last_id == "":
            last_id = rule["id"]
            if rule["type"] == "1":
                text += rule["text"]
    if text != "":
        t["id"] = last_id
        t["text"] = text
        t["label"] = ""
        tci.append(t)
    json.dump(tci, open(tci_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)




if __name__ == "__main__":
    sco_to_tci("rules_cache/sco.json", "rules_cache/tci.json")
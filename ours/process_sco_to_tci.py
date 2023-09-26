import json

# 将sequence classification output的结果组合成token classification input的格式

def sco_to_tci(sco: list):
    last_id = ""
    text = ""
    tci = []
    t = {}
    for rule in sco:
        if "id" not in rule:
            continue
        rule["id"] = rule["id"].split("_")[0]
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
    return tci




if __name__ == "__main__":
    sco_data = json.load(open("rules_cache/sco.json", "r", encoding="utf-8"))
    tci_data = sco_to_tci(sco_data)
    json.dump(tci_data, open("rules_cache/tci.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
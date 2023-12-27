from ours.process_tci_to_tco import token_classification
from ours.process_tco_to_r1 import read_OBI_to_rule
import json

with open("rules_cache/数据.txt") as f:
    lines = f.readlines()

datas = []
i=0
for line in lines:
    if line.find("条件") == 2:
        datas.append({
            "id": i,
            "text": line[5:].strip(), 
            "label": ""
        })
        i += 1

# json.dump(datas, open("tci.json", "r", encoding="utf-8"), ensure_ascii=False, indent=4)
knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
tco = token_classification(datas, knowledge, "../model/ours/best_1701809213", "../data/tc_data.dict")
# json.dump(tco, open("tco.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

f = open("输出.txt", "w", encoding="utf-8")
for data in tco:
    text = data['text']
    label = data['label']
    stack, _, _, _, _, _ = read_OBI_to_rule(text, label)
    f.write(f"{data['id']}\n")
    f.write(f"{stack}\n\n")
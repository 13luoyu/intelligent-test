import json

j1 = json.load(open("深圳证券交易所公开募集基础设施证券.json", "r", encoding="utf-8"))
j2 = json.load(open("finish_深圳证券交易所公开募集基础设施证券.json", "r", encoding="utf-8"))

for j, data in enumerate(j2):
    if "id" in data:
        data["id"] = j1[j]["id"]

json.dump(j2, open("t", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
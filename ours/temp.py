import json

a = open("rules_cache/r3.mydsl", "r", encoding="utf-8").read()
json.dump({"data":a}, open("rules_cache/consistency_checking_input.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
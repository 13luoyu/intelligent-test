import json

knowledge = json.load(open("knowledge.json", "r", encoding="utf-8"))

other_know = {}

for k in list(knowledge.keys()):
    if isinstance(knowledge[k], str):
        other_know[k] = knowledge[k]
    elif k == "authority" or k == "stateMachine":
        other_know[k] = knowledge[k]

json.dump(other_know, open("other_knowledge.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
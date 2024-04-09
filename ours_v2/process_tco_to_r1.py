import json
from transfer.knowledge_tree import encode_tree


def compose_knowledge(tco, knowledge):
    ...
    knowledge = encode_tree(knowledge)
    for data in tco:
        label = data["label"]
        new_label = ""
        for item in label.split(","):
            key = item.split(":")[0]
            value = ":".join(item.split(":")[1:])
            # 借助领域知识，将value转换为对应的具体标签
            if key == "value":
                for know in knowledge:
                    k, v = know["content"].split(":")[0], know["content"].split(":")[1]
                    if key == v:


    return tco



if __name__ == '__main__':
    tco = json.load(open("cache/tco.json"))
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json"))
    tco_with_know = compose_knowledge(tco, knowledge)
    json.dump(tco_with_know, open("cache/tco_with_know.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)
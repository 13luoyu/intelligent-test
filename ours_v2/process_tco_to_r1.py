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
            # 并处理其他...
            if key == "value":
                if "其他" in value and value.count("其他") == 1:
                    value_part = value.split("其他")[1]
                    find = False
                    for know in knowledge:
                        k, v = know["content"].split(":")[0], know["content"].split(":")[1]
                        if value_part == v or value_part == k:
                            new_label += f"{k}:{value},"
                            find = True
                            break
                    if not find:
                        new_label += f"{key}:{value},"
                    continue
                # elif "其他" not in value 没有“其他”，这里不考虑多个“其他”的情况
                find = False
                for know in knowledge:
                    k, v = know["content"].split(":")[0], know["content"].split(":")[1]
                    if value == v:
                        new_label += f"{k}:{value},"
                        find = True
                        break
                if not find:
                    new_label += f"{key}:{value},"
            
            else:
                new_label += f"{key}:{value},"
        data["label"] = new_label[:-1]

    return tco



if __name__ == '__main__':
    tco = json.load(open("cache/tco.json"))
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json"))
    tco_with_know = compose_knowledge(tco, knowledge)
    json.dump(tco_with_know, open("cache/tco_with_know.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)
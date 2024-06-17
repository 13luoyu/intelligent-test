import json
from transfer.knowledge_tree import encode_tree

# 为../data/data_for_LLM_v2/ir_annotation_v2.json添加领域知识，生成../data/data_for_LLM_v2/ir_annotation_v2_with_knowledge.json

def add_knowledge_v2(rules, knowledge, answer_key):
    knowledge = encode_tree(knowledge)
    for data in rules:
        label = data[answer_key]
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
                if "方式" in value[-2:] and len(value) > 4:
                    value = value[:-2]
                to_add_label = ""
                for know in knowledge:
                    k, v = know["content"].split(":")[0], know["content"].split(":")[1]
                    if "指令" in k or "要素" in k:
                        continue
                    if value == v or v in value and value.index(v) == 0 and len(value) - len(v) <= 2:
                        if k == "证券品种" and to_add_label != "":
                            continue
                        to_add_label = f"{k}:{value},"
                        find = True
                new_label += to_add_label
                if not find:
                    new_label += f"{key}:{value},"
            
            else:
                new_label += f"{key}:{value},"
        data[answer_key] = new_label[:-1]
    return rules



if __name__ == "__main__":
    rules = json.load(open("../data/data_for_LLM_v2/ir_annotation_v2.json"))
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json"))
    rules = add_knowledge_v2(rules, knowledge, answer_key="answer")
    json.dump(rules, open("../data/data_for_LLM_v2/ir_annotation_v2_with_knowledge.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)
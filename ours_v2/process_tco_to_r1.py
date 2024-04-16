import json
from transfer.knowledge_tree import encode_tree
from support.add_knowledge import add_knowledge_v2




if __name__ == '__main__':
    tco = json.load(open("cache/tco.json"))
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json"))
    add_knowledge_v2(tco, knowledge, answer_key="label")
    json.dump(tco_with_know, open("cache/tco_with_know.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)
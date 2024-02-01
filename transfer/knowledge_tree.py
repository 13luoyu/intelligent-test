import json

knowledge_file = "../data/knowledge.json"
knowledge_tree_file = "../data/knowledge_tree.json"

def encode_tree(knowledge):
    know = {}
    for key in list(knowledge.keys()):
        if isinstance(knowledge[key], list) and key != "stateMachine" and key != "authority":
            know[key] = knowledge[key]
    json.dump(know, open("temp.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)


    exit(0)





def decode_tree(knowledge_tree):
    ...




if __name__ == "__main__":
    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    knowledge_tree = encode_tree(knowledge)
    json.dump(open(knowledge_tree_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # knowledge = decode_tree(knowledge_tree)
    # json.dump(open(knowledge_tree_file + "_decode", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
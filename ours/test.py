from ours.process_r1_to_r2 import construct_tree
import json

knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
arr = construct_tree(knowledge, "权证")
print(arr)
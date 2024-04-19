import json
a = json.load(open("ir_annotation_v2_with_knowledge.json", "r", encoding="utf-8"))

b = json.load(open("assemble_annotation_v2.json", "r", encoding="utf-8"))
for i, data in enumerate(a):
    prompt, rule = data['prompt'].split("\n")[0], data['prompt'].split("\n")[1]
    rule_elements = data['answer']
    prompt = "给出一条规则及其中的规则元素，请你将规则元素互相组合并写成R规则的形式。如果组合后的R规则存在冲突，则将其分成多条不冲突的R规则。"
    data['prompt'] = prompt + "\n" + rule + "\n规则元素:" + rule_elements
    data['answer'] = b[i]['answer']

json.dump(a, open("assemble_annotation_v2.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
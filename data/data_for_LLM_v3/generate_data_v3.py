import json


datas = json.load(open("../data_for_LLM_v2/assemble_annotation_v2.1.json", "r", encoding="utf-8"))
for data in datas:
    rule = data['prompt'].split("\n")[1]
    data['prompt'] = f"给出一条规则，请你抽取其中的规则元素并组合成R规则的形式。如果组合后的R规则存在冲突，则将其分成多条不冲突的R规则。\n{rule}"
json.dump(datas, open("ir_assemble_annotation_v3.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
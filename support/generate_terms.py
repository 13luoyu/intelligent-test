import json

def generate_terms(datas):
    terms = []
    for data in datas:
        answer = data['answer'].replace(" ", "").split("\n")[0]
        values = [":".join(v.split(":")[1:]) for v in answer.split(",")]
        terms += values
    return terms

if __name__ == "__main__":
    datas = json.load(open("../data/data_for_LLM_v2/ir_annotation.json", "r", encoding="utf-8"))
    terms = generate_terms(datas)
    with open("../data/domain_knowledge/terms.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(terms))
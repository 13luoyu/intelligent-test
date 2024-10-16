import json
from ours.main import nlp_process, alg_process
import time


def load_data(data_file):
    data = json.load(open(data_file, "r", encoding="utf-8"))
    for d in data:
        _, setting, rule = d['prompt'].split("\n")
        market, variety = setting.split("，")
        market = market.split("：")[1]
        variety = variety.split("：")[1][:-1]
        rule = ":".join(rule.split(":")[1:])
        r2 = d['answer']
        yield market, variety, rule, r2



def post_process(r2):
    new_r2 = ""
    lines = r2.split("\n")
    index = 1
    for line in lines:
        if "rule" in line:
            new_r2 += f"rule {index}\n"
            index += 1
        elif "if" in line or "then" in line:
            new_r2 += f"{line.strip()}\n"
    new_r2 = new_r2.replace("'", "").strip()
    return new_r2


def generate_r2_llm4fin(data_file):
    tc_model_path = "../model/trained/mengzi_rule_element_extraction"
    sc_model_path = "../model/trained/mengzi_rule_filtering"

    log = open("r2/llm4fin.log", "w", encoding="utf-8")
    begin_time = time.time()
    output = []

    for i, (market, variety, rule, label) in enumerate(load_data(data_file)):
        with open("cache/data.txt", "w", encoding="utf-8") as f:
            f.write(f"{market}{variety}交易规则\n")
            f.write(f"1.1 " + rule)
        nlp_process("cache/data.txt", "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/terms.txt", sc_model_path, tc_model_path, "../data/data_for_LLM_encoder/tc_data.dict")
        
        alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"cache/r3.mydsl", f"cache/r3.json", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/knowledge.json", "cache/relation.json", "cache/explicit_relation.json", "cache/implicit_relation.json", concretize_securities=True)

        r2 = open("cache/r2.mydsl", "r", encoding="utf-8").read()
        r2 = post_process(r2)
        output.append({
            "id": i,
            "rule": rule,
            "prediction": r2,
            "label": label
        })
        log.write(json.dumps(output[-1], ensure_ascii=False, indent=4) + "\n\n")
        log.flush()

    time_consume = time.time() - begin_time
    print(f"总共消耗时间: {time_consume}")
    log.write(f"总共消耗时间: {time_consume}\n")
    log.close()
    json.dump(output, open("r2/llm4fin.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)


def generate_r1_llm4fin_sdp(data_file):
    tc_model_path = "../model/trained/mengzi_rule_element_extraction"
    sc_model_path = "../model/trained/mengzi_rule_filtering"

    log = open("r2/llm4fin_sdp.log", "w", encoding="utf-8")
    begin_time = time.time()
    output = []

    for i, (market, variety, rule, label) in enumerate(load_data(data_file)):
        with open("cache/data.txt", "w", encoding="utf-8") as f:
            f.write(f"{market}{variety}交易规则\n")
            f.write(f"1.1 " + rule)
        nlp_process("cache/data.txt", "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/terms.txt", sc_model_path, tc_model_path, "../data/data_for_LLM_encoder/tc_data.dict", use_sdp=True)
        
        alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"cache/r3.mydsl", f"cache/r3.json", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/knowledge.json", "cache/relation.json", "cache/explicit_relation.json", "cache/implicit_relation.json", concretize_securities=True)

        r2 = open("cache/r2.mydsl", "r", encoding="utf-8").read()
        r2 = post_process(r2)
        output.append({
            "id": i,
            "rule": rule,
            "prediction": r2,
            "label": label
        })
        log.write(json.dumps(output[-1], ensure_ascii=False, indent=4) + "\n\n")
        log.flush()

    time_consume = time.time() - begin_time
    print(f"总共消耗时间: {time_consume}")
    log.write(f"总共消耗时间: {time_consume}\n")
    log.close()
    json.dump(output, open("r2/llm4fin_sdp.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)


if __name__ == "__main__":
    generate_r2_llm4fin("data/r2_data.json")
    generate_r1_llm4fin_sdp("data/r2_data.json")
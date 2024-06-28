import argparse
from ours.main import nlp_process, alg_process
import time
import os



def add_trading_method(file, trading_method):
    data = open(file, "r", encoding="utf-8").read()
    data = f"define 交易方式 = {trading_method}\n{data}"
    with open(file, "w", encoding="utf-8") as f:
        f.write(data)


def generate_rules_testcases_for_experiment():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default="mengzi", choices=["mengzi", "finbert", "llama2"])
    args = parser.parse_args()
    if args.model == "mengzi":
        tc_model_path = "../model/trained/mengzi_rule_element_extraction"
    elif args.model == "finbert":
        tc_model_path = "../model/trained/finbert_rule_element_extraction"
    elif args.model == "llama2":
        tc_model_path = "../model/trained/llama2_rule_element_extraction"
    else:
        raise ValueError(f"需要设置参数 --model 为 'mengzi', 'finbert', 'llama2' 之一")
    sc_model_path = "../model/trained/mengzi_rule_filtering"

    time_log = open("log/time.log", "w", encoding="utf-8")

    for file in sorted(os.listdir("data/")):
        if ".txt" in file:
            # if "data4" not in file:
            #     continue
            filename = file[:-4]
            begin_time = time.time()
            nlp_process("data/" + file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/terms.txt", sc_model_path, tc_model_path, "../data/data_for_LLM_encoder/tc_data.dict")
            first_line = open("data/"+file, "r", encoding="utf-8").readlines()[0].strip()
            if "盘后定价交易" in first_line:
                add_trading_method(f"cache/r1.mydsl", "盘后定价交易")
            elif "大宗交易" in first_line:
                add_trading_method(f"cache/r1.mydsl", "大宗交易")
            elif "竞价交易" in first_line:
                add_trading_method(f"cache/r1.mydsl", "竞价交易")

            alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"rules_and_testcases_for_experiment/{filename}_rules_{args.model}.mydsl", f"rules_and_testcases_for_experiment/{filename}_testcases_{args.model}.json", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/knowledge.json", "cache/relation.json", "cache/explicit_relation.json", "cache/implicit_relation.json", concretize_securities=True)
            time_consume = time.time() - begin_time
            print(f"《{filename}》总共消耗时间: {time_consume}")
            time_log.write(f"《{filename}》总共消耗时间: {time_consume}\n")
    time_log.close()




if __name__ == "__main__":
    generate_rules_testcases_for_experiment()
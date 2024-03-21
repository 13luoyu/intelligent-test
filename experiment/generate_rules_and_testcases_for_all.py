from ours.main import nlp_process, alg_process
import time
import os
import argparse

def generate_rules_testcases_for_all():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default="mengzi", choices=["mengzi", "finbert", "llama"])
    args = parser.parse_args()
    if args.model == "mengzi":
        tc_model_path = "../model/ours/mengzi_rule_element_extraction"
    elif args.model == "finbert":
        tc_model_path = "../model/ours/mengzi_rule_element_extraction"
    elif args.model == "llama":
        tc_model_path = "../lora/output/best_model_dev_dev_acc0_9792"
    else:
        raise ValueError(f"需要设置参数 --model 为 'mengzi', 'finbert', 'llama' 之一")
    
    for file in os.listdir("data/"):
        if ".pdf" in file:
            # if "深圳证券交易所交易规则" not in file:
            #     continue
            filename = file[:-4]
            print(f"文件《{filename}》开始执行")
            begin_time = time.time()
            nlp_process("data/" + file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/classification_knowledge.json", "../data/terms.txt", "../model/ours/mengzi_rule_filtering", tc_model_path, "../data/tc_data.dict")
            alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"rules_and_testcases_for_all/{filename}_rules.mydsl", f"rules_and_testcases_for_all/{filename}_testcases.json", "../data/classification_knowledge.json", "../data/knowledge.json", "cache/relation.json", "cache/explicit_relation.json", "cache/implicit_relation.json")
            time_consume = time.time() - begin_time
            print(f"《{filename}》总共消耗时间: {time_consume}")



if __name__ == "__main__":
    generate_rules_testcases_for_all()
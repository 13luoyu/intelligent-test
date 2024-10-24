# 主程序
from ours.process_nl_to_sci import nl_to_sci
from ours.process_sci_to_sco import sequence_classification
from ours.process_sco_to_tci import sco_to_tci
from ours.process_tci_to_tco import token_classification_encoder, token_classification_decoder
from ours.process_tco_to_r1 import to_r1
from ours.process_tco_to_r1_v2 import to_r1 as to_r1_sdp
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2
from ours.process_r2_to_r3 import compose_rules_r2_r3
from ours.process_r3_to_testcase import testcase
from ours.process_testcase_to_outputs import generate_dicts
from transfer import mydsl_to_rules, rules_to_mydsl
import json
from pprint import pprint
import time
import argparse
import os

def add_defines(s, market_variety):
    s = f"define 交易市场 = {market_variety['market']}\ndefine 交易品种 = {market_variety['variety']}\n\n{s}"
    return s

def nlp_process(input_file: str, 
                setting_file: str,
                sci_file: str, 
                sco_file: str, 
                tci_file: str, 
                tco_file: str, 
                r1_file: str, 
                knowledge_file: str, 
                terms_file,
                sc_model: str,
                tc_model: str, 
                tc_dict: str, 
                batch_size: int = 8,
                sentence_max_length: int = 512,
                use_sdp: bool = False):
    # 获取输入，转换为句分类的输入格式
    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    if ".txt" in input_file:
        input_data = open(input_file, "r", encoding="utf-8").read()
        sci, market_variety = nl_to_sci(nl_data=input_data, knowledge=knowledge)
    else:
        sci, market_variety = nl_to_sci(nl_file=input_file, knowledge=knowledge)
    json.dump(sci, open(sci_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(market_variety, open(setting_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    # 句分类任务
    # 标注每个句子的类别：0为无法测试的自然语言，1为可测试的规则，2为领域知识
    sco = sequence_classification(sci, sc_model, batch_size, sentence_max_length)
    json.dump(sco, open(sco_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    print("规则筛选任务完成")
    # 将句子按照id组合
    tci = sco_to_tci(sco)
    json.dump(tci, open(tci_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    # 标注句子中每个字的类别
    terms = open(terms_file, "r", encoding="utf-8").read().split("\n")
    if "mengzi" in tc_model or "finbert" in tc_model:
        tco = token_classification_encoder(tci, knowledge, tc_model, tc_dict, batch_size, sentence_max_length)
    else:  # llama2
        tco = token_classification_decoder(tci, tc_model, knowledge, use_algorithm=True)
    json.dump(tco, open(tco_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    print("规则元素抽取任务完成")
    # 调用转R1
    if not use_sdp:
        r1 = to_r1(tco, knowledge, terms)
    else:
        r1 = to_r1_sdp(tco, knowledge, terms)
    r1 = add_defines(r1, market_variety)
    with open(r1_file, "w", encoding="utf-8") as f:
        f.write(r1)
    print("R规则生成")
    # exit(0)

def alg_process(r1_mydsl_file, r1_json_file, r2_json_file, r2_mydsl_file, r3_json_file, r3_mydsl_file, testcase_file, classification_knowledge_file, knowledge_file, relation_file, e_relation_file, i_relation_file, concretize_securities=False):
    # 读文件
    r1 = open(r1_mydsl_file, "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r1)
    # 领域知识
    classification_knowledge = json.load(open(classification_knowledge_file, "r", encoding="utf-8"))
    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    # 文件预处理，将rules中某些自然语言描述的规则转换为数学表达式
    rules, vars = preprocess(rules, vars)
    json.dump(rules, open(r1_json_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    print(f"R1包含规则数：{len(rules)}")

    # R1->R2
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, classification_knowledge, concretize_securities)
    json.dump(rules, open(r2_json_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    r2_rules = rules
    r2_json = rules_to_mydsl.r2_to_json(r2_rules)
    r2 = rules_to_mydsl.rules_to_mydsl(r2_json)
    with open(r2_mydsl_file, "w", encoding="utf-8") as f:
        f.write(r2)
    print(f"R2规则生成，包含规则数：{len(rules)}")

    # R2->R3
    defines, vars, rules, implicit_relation_count, explicit_relation_count, relation, implicit_relation, explicit_relation = compose_rules_r2_r3(defines, vars, rules, knowledge)
    json.dump(rules, open(r3_json_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    r3_rules = rules
    r3_json = rules_to_mydsl.r3_to_json(r3_rules)
    r3 = rules_to_mydsl.rules_to_mydsl(r3_json)
    with open(r3_mydsl_file, "w", encoding="utf-8") as f:
        f.write(r3)
    print(f"R3规则生成，包含规则数：{len(rules)}")
    print(f"显式关系有{explicit_relation_count}条，隐式关系有{implicit_relation_count}条")
    json.dump(relation, open(relation_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(explicit_relation, open(e_relation_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(implicit_relation, open(i_relation_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    r3_time = time.time()
    
    # 生成测试样例
    vars = testcase(defines, vars, rules)
    print("测试数据生成")
    outputs = generate_dicts(vars, rules)

    # 保存结果
    out_num = 0
    for o in outputs:
        out_num += len(o)
    print(f"testcase生成，数目为：{out_num}")
    json.dump(outputs, open(testcase_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    
    return r3_time


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default="mengzi", choices=["mengzi", "finbert", "llama2"])
    parser.add_argument("--file", type=str, default="./download_files/深圳证券交易所债券交易规则.pdf")
    parser.add_argument("--use_sdp", type=bool, default=False)
    args = parser.parse_args()
    if args.model == "mengzi":
        tc_model_path = "../model/trained/mengzi_rule_element_extraction"
    elif args.model == "finbert":
        tc_model_path = "../model/trained/finbert_rule_element_extraction"
    elif args.model == "llama2":
        tc_model_path = "../model/trained/llama2_rule_element_extraction"
    else:
        raise ValueError(f"需要设置参数 --model 为 'mengzi', 'finbert', 'llama2' 之一")
    if not os.path.exists(args.file):
        raise FileNotFoundError(f"文件 {args.file} 不存在")
    
    begin_time = time.time()
    nlp_process(args.file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/terms.txt", "../model/trained/mengzi_rule_filtering", tc_model_path, "../data/data_for_LLM_encoder/tc_data.dict", use_sdp=args.use_sdp)
    alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", "cache/r3.mydsl", "cache/testcase.json", "../data/domain_knowledge/classification_knowledge.json", "../data/domain_knowledge/knowledge.json", "cache/relation.json", "cache/explicit_relation.json", "cache/implicit_relation.json")
    time_consume = time.time() - begin_time
    print(f"总共消耗时间: {time_consume}")
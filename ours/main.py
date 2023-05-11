# 主程序
from process_nl_to_sci import nl_to_sci
from process_sci_to_sco import sequence_classification
from process_sco_to_tci import sco_to_tci
from process_tci_to_tco import token_classification
from process_tco_to_r1 import to_r1

from process_r1_to_r2 import preprocess, compose_rules_r1_r2
from process_r2_to_r3 import compose_rules_r2_r3
from process_r3_to_testcase import testcase
from process_testcase_to_outputs import generate_dicts
from transfer import mydsl_to_rules
import json
from pprint import pprint


def nlp_process(input_file, sci_file, sco_file, tci_file, tco_file, r1_file, knowledge_file):
    # 获取输入，转换为句分类的输入格式
    nl_to_sci(input_file, sci_file)
    # 句分类任务
    # 标注每个句子的类别：0为无法测试的自然语言，1为可测试的规则，2为领域知识
    sequence_classification(sci_file, sco_file)
    # 将句子按照id组合
    sco_to_tci(sco_file, tci_file)
    # 标注句子中每个字的类别
    token_classification(tci_file, tco_file, knowledge_file)
    # 调用转R1
    to_r1(tco_file, r1_file, knowledge_file)

def alg_process(input_file, r1_file, r2_file, r3_file, testcase_file, knowledge_file):
    # 读文件
    defines, vars, rules = mydsl_to_rules.read_file(input_file)
    # 领域知识
    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    # 文件预处理，将rules中某些自然语言描述的规则转换为数学表达式
    rules = preprocess(rules)
    json.dump(rules, open(r1_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # R1->R2
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
    json.dump(rules, open(r2_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # R2->R3
    defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
    json.dump(rules, open(r3_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # 生成测试样例
    vars = testcase(defines, vars, rules)
    outputs = generate_dicts(vars, rules)
    pprint(vars)

    # 保存结果
    out_num = 0
    for o in outputs:
        out_num += len(o)
    print(f"testcase包含的规则数：{out_num}")
    json.dump(outputs, open(testcase_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)



if __name__ == "__main__":
    nlp_process("rules_cache/input.txt", "rules_cache/sci.json", "rules_cache/sco.json", "rules_cache/tci.json", "rules_cache/tco.json", "rules_cache/r1.mydsl", "../data/knowledge.json")
    alg_process("rules_cache/r1.mydsl", "rules_cache/r1.txt", "rules_cache/r2.txt", "rules_cache/r3.txt", "rules_cache/testcase.txt", "../data/knowledge.json")
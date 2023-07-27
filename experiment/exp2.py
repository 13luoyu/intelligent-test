# 生成规则，并比较数目和质量
# 质量的比较比较松
from experiment.compare_BR import compute_BR_num, compute_BR_precision
from transfer import mydsl_to_rules
import json
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2
from ours.process_r2_to_r3 import compose_rules_r2_r3
from transfer.rules_to_json_and_mydsl import r2_to_json, r3_to_json, to_mydsl

if __name__ == "__main__":
    fp = open("data/exp2_result.log", "w", encoding="utf-8")

    # print("我们的结果：")
    # fp.write("我们的结果：\n")
    # # 生成BR
    # defines, vars, rules = mydsl_to_rules.read_file("data/exp1_3_r1.mydsl")
    # knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    # rules, vars = preprocess(rules, vars)
    # defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
    # r2_json = r2_to_json(rules)
    # to_mydsl(r2_json, "data/exp2_r2.mydsl")
    # defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
    # r3_json = r3_to_json(rules)
    # to_mydsl(r3_json, "data/exp2_r3.mydsl")
    # # 计算BR的数目
    # compute_BR_num("data/exp2_r3.mydsl", fp)
    # # 将BR中的约束子句提取出来，并与正确的用例比较，看准确率是多少
    # compute_BR_precision("data/exp2_r3.mydsl", "data/exp2_expert.txt", fp)

    # Sage
    print("Sage: ")
    fp.write("Sage: \n")
    compute_BR_num("data/exp2_QA_sage.txt", fp)
    compute_BR_precision("data/exp2_QA_sage.txt", "data/exp2_expert.txt", fp)

    # Claude
    print("Claude: ")
    fp.write("Claude: \n")
    compute_BR_num("data/exp2_QA_claude.txt", fp)
    compute_BR_precision("data/exp2_QA_claude.txt", "data/exp2_expert.txt", fp)

    # ChatGPT
    print("ChatGPT: ")
    fp.write("ChatGPT: \n")
    compute_BR_num("data/exp2_QA_chatgpt.txt", fp)
    compute_BR_precision("data/exp2_QA_chatgpt.txt", "data/exp2_expert.txt", fp)

    fp.close()
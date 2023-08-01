# 生成规则，并比较数目和质量
# 质量的比较比较松
import os
from experiment.compare_BR import compute_BR_num, compute_BR_precision
from transfer import mydsl_to_rules
import json
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2
from ours.process_r2_to_r3 import compose_rules_r2_r3
from transfer.rules_to_json_and_mydsl import r2_to_json, r3_to_json, to_mydsl

if __name__ == "__main__":
    fp = open("data/exp2_result.log", "w", encoding="utf-8")

    # # 统计专家用例的数量
    # print("Domain Expert: ")
    # fp.write("Domain Expert: \n")
    # compute_BR_num("data/exp2_expert.txt", fp)

    # # 统计非专家用例的数量和正确率
    # print("Non-Expert: ")
    # fp.write("Non-Expert: \n")
    # compute_BR_num("data/exp2_non-expert.txt", fp)
    # compute_BR_precision("data/exp2_non-expert.txt", "data/exp2_expert.txt", fp)

    # # Sage
    # print("Sage: ")
    # fp.write("Sage: \n")
    # compute_BR_num("data/exp2_QA_sage.txt", fp)
    # compute_BR_precision("data/exp2_QA_sage.txt", "data/exp2_expert.txt", fp)

    # # Claude
    # print("Claude: ")
    # fp.write("Claude: \n")
    # compute_BR_num("data/exp2_QA_claude.txt", fp)
    # compute_BR_precision("data/exp2_QA_claude.txt", "data/exp2_expert.txt", fp)

    # # ChatGPT
    # print("ChatGPT: ")
    # fp.write("ChatGPT: \n")
    # compute_BR_num("data/exp2_QA_chatgpt.txt", fp)
    # compute_BR_precision("data/exp2_QA_chatgpt.txt", "data/exp2_expert.txt", fp)



    print("我们的结果：")
    fp.write("我们的结果：\n")
    output = open("data/exp2_output.txt", "w", encoding="utf-8")
    for file in sorted(os.listdir("data/")):
        if "exp2_input" in file and "r1" in file:
            # 生成BR
            defines, vars, rules = mydsl_to_rules.read_file(f"data/{file}")
            knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
            rules, vars = preprocess(rules, vars)
            defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
            r2_json = r2_to_json(rules)
            to_mydsl(r2_json, f"data/{file[:11]}_r2.mydsl")
            defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
            r3_json = r3_to_json(rules)
            to_mydsl(r3_json, f"data/{file[:11]}_r3.mydsl")
            with open(f"data/{file[:11]}_r3.mydsl", "r", encoding="utf-8") as f:
                cnt = f.read()
                output.write(f"dataset{file[10]}\n\n\n")
                output.write(cnt + "\n\n\n\n\n\n\n\n\n")
        # if "exp2_cinput" in file and "r1" in file:
        #     # 生成BR
        #     defines, vars, rules = mydsl_to_rules.read_file(f"data/{file}")
        #     knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
        #     rules, vars = preprocess(rules, vars)
        #     defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
        #     r2_json = r2_to_json(rules)
        #     to_mydsl(r2_json, f"data/{file[:12]}_r2.mydsl")
        #     defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
        #     r3_json = r3_to_json(rules)
        #     to_mydsl(r3_json, f"data/{file[:12]}_r3.mydsl")
        #     with open(f"data/{file[:12]}_r3.mydsl", "r", encoding="utf-8") as f:
        #         cnt = f.read()
        #         output.write(f"dataset{file[11]}\n\n\n")
        #         output.write(cnt + "\n\n\n\n\n\n\n\n\n")
    output.close()
    # 计算BR的数目
    compute_BR_num("data/exp2_output.txt", fp)
    # 将BR中的约束子句提取出来，并与正确的用例比较，看准确率是多少
    compute_BR_precision("data/exp2_output.txt", "data/exp2_expert.txt", fp)


    fp.close()
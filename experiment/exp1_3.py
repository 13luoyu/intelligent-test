# 生成规则，并比较数目和质量
# 质量的比较比较松
from ours.process_tco_to_r1 import to_r1
from experiment.compare_BR import compute_BR_num, compute_BR_precision




if __name__ == "__main__":
    fp = open("data/exp1_3_result.log", "w", encoding="utf-8")

    # Sage
    print("Sage: ")
    fp.write("Sage: \n")
    compute_BR_num("data/exp1_3_sage.txt", fp)
    compute_BR_precision("data/exp1_3_sage.txt", "data/exp1_3_correct.mydsl", fp)

    # Claude
    print("Claude: ")
    fp.write("Claude: \n")
    compute_BR_num("data/exp1_3_claude.txt", fp)
    compute_BR_precision("data/exp1_3_claude.txt", "data/exp1_3_correct.mydsl", fp)

    # ChatGPT
    print("ChatGPT: ")
    fp.write("ChatGPT: \n")
    compute_BR_num("data/exp1_3_chatgpt.txt", fp)
    compute_BR_precision("data/exp1_3_chatgpt.txt", "data/exp1_3_correct.mydsl", fp)

    print("我们的结果：")
    fp.write("我们的结果：\n")
    # 生成BR
    to_r1("../data/rules.json", "data/exp1_3_correct.mydsl", "../data/knowledge.json")
    to_r1("data/exp1_2_output.json", "data/exp1_3_r1.mydsl", "../data/knowledge.json")
    # 计算BR的数目
    compute_BR_num("data/exp1_3_r1.mydsl", fp)
    # 将BR中的约束子句提取出来，并与正确的用例比较，看准确率是多少
    compute_BR_precision("data/exp1_3_r1.mydsl", "data/exp1_3_correct.mydsl", fp)


    fp.close()
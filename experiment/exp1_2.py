import json
from ours.process_tci_to_tco import token_classification
import time

# 将信息抽取任务的预测和真实值放在一个文件中
def integrate_tc(real_file, hat_file, out_file):
    rule1 = json.load(open(real_file, "r", encoding="utf-8"))
    rule2 = json.load(open(hat_file, "r", encoding="utf-8"))

    f = open(out_file, "w", encoding="utf-8")

    f.write("比较结果：\n\n")
    for i, rule in enumerate(rule1):
        if "id" in rule:
            f.write(f"id: {rule['id']}\n")
        f.write(f"text: {rule['text']}\n")
        f.write(f"ir hat: {rule2[i]['label']}\n")
        f.write(f"ir real: {rule['label']}\n\n")

    f.close()



# 给定信息抽取模型的输出，计算正确标签的信息数、模型预测的信息数、正确的数目，
# 并由此计算正确率、召回率以及F1分数。
def evaluate(in_file, out_file):
    with open(in_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    # 该条正确的信息数、预测的信息数、正确的数目
    real_info, hat_info, correct_info = [], [], []
    for line in lines:
        if "ir hat" in line:
            line = line[8:-1]
            hats = line.split(" ")
        elif "ir real" in line:
            line = line[9:-1]
            reals = line.split(" ")
            # 如果label、开始位置、结束位置、中间每个元素完全一样，视为信息正确
            # 首先从hats和reals中提取信息，存入数组。数组的每个元素为（信息，信息开始，信息结束）

            def compute_info(labels):
                infos = []
                last = "O"
                a, b = 0, 0  # 句子的开始和结束
                for i, label in enumerate(labels):
                    if label == "O":
                        if last != "O":
                            b = i
                            infos.append((last, a, b))
                        last = label
                    else:
                        l = label[2:]
                        if "B-" in label:
                            if last != "O":
                                b = i
                                infos.append((last, a, b))
                            a = i
                            last = l
                        else:
                            ...
                return infos
            info_hats = compute_info(hats)
            info_reals = compute_info(reals)
            
            real_info.append(len(info_reals))
            hat_info.append(len(info_hats))

            correct_num = 0
            for info in info_hats:
                if info in info_reals:
                    correct_num += 1
            correct_info.append(correct_num)
    real_sum, hat_sum, correct_sum = sum(real_info), sum(hat_info), sum(correct_info)
    precision = correct_sum / hat_sum
    recall = correct_sum / real_sum
    F1 = 2 * precision * recall / (precision + recall)
    with open(out_file, "w", encoding="utf-8") as f:
        f.write(f"真实信息总数：{hat_sum}，预测信息总数：{real_sum}，其中完全正确的信息数：{correct_sum}，正确率{round(precision, 3)}，召回率{round(recall, 3)}，F1分数{round(F1, 3)}。")
    print(f"真实信息总数：{hat_sum}，预测信息总数：{real_sum}，其中完全正确的信息数：{correct_sum}，正确率{round(precision, 3)}，召回率{round(recall, 3)}，F1分数{round(F1, 3)}。")




if __name__ == "__main__":
    # 执行信息抽取
    token_classification("data/exp1_2_input.json", "data/exp1_2_output.json", "../data/knowledge.json", "../model/ours/best_1689080207", "../data/tc_data.dict")
    # 整合预测与真实值
    integrate_tc("../data/rules.json", "data/exp1_2_output.json", "data/exp1_2_compare.log")
    # 评估
    evaluate("data/exp1_2_compare.log", "data/exp1_2_result.log")
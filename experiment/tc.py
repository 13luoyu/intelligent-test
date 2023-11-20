import json
from ours.process_tci_to_tco import token_classification
import os
import nltk

def edit_distance(s1, s2):
    """
    衡量两个字符串的相似度，计算两个字符串的编辑距离。编辑距离指的是将一个字符串转换成另一个字符串所需的最少操作次数，包括插入、删除、替换操作。
    """
    return nltk.edit_distance(s1, s2)
    # len1, len2 = len(s1), len(s2)
    # dp = [[0] * (len2+1) for _ in range(len1+1)]
    # for i in range(len1+1):
    #     dp[i][0] = i
    # for j in range(len2+1):
    #     dp[0][j] = j
    # for i in range(1, len1+1):
    #     for j in range(1, len2+1):
    #         if s1[i-1] == s2[j-1]:
    #             dp[i][j] = dp[i-1][j-1]
    #         else:
    #             dp[i][j] = min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1]) + 1
    # return dp[len1][len2]

def str_same(s1, s2, threshold):
    # s1是预测值，s2是真实值
    distance = edit_distance(s1, s2)
    score = 1 - (distance / max(len(s1), len(s2)))
    if score >= threshold:
        return True
    else:
        return False

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
def evaluate(in_file, out_file, threshold=0.8):
    with open(in_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    # 该条正确的信息数、预测的信息数、正确的数目
    real_info, hat_info, correct_info = [], [], []
    for line in lines:
        if "text" in line:
            text = line[6:-1]
        if "ir hat" in line:
            line = line[8:-1]
            hats = line.split(" ")
        elif "ir real" in line:
            line = line[9:-1]
            reals = line.split(" ")
            # 首先从hats和reals中提取信息，存入数组。数组的每个元素为（信息，信息开始，信息结束）

            def compute_info(labels):
                infos = []
                last = "O"
                a, b = 0, 0  # 句子的开始和结束
                for i, label in enumerate(labels):
                    if label == "O":
                        if last != "O":
                            b = i
                            infos.append((last, text[a:b]))
                        last = label
                    else:
                        l = label[2:]
                        if "B-" in label:
                            if last != "O":
                                b = i
                                infos.append((last, text[a:b]))
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
                # 这是精确匹配
                # if info in info_reals:
                    # correct_num += 1
                # 模糊匹配，信息只要大部分被抽取出来就认为正确
                for info1 in info_reals:
                    if str_same(info[1], info1[1], threshold):
                        correct_num += 1
                        break
            correct_info.append(correct_num)
    real_sum, hat_sum, correct_sum = sum(real_info), sum(hat_info), sum(correct_info)
    precision = correct_sum / hat_sum
    recall = correct_sum / real_sum
    F1 = 2 * precision * recall / (precision + recall)
    with open(out_file, "w", encoding="utf-8") as f:
        f.write(f"真实信息总数：{real_sum}，预测信息总数：{hat_sum}，其中正确的信息数：{correct_sum}，正确率{round(precision, 4)}，召回率{round(recall, 4)}，F1分数{round(F1, 4)}。")
    print(f"真实信息总数：{real_sum}，预测信息总数：{hat_sum}，其中完全正确的信息数：{correct_sum}，正确率{round(precision, 4)}，召回率{round(recall, 4)}，F1分数{round(F1, 4)}。")




if __name__ == "__main__":

    for file in sorted(os.listdir('../model/ours/')):
        if file == 'best_1690658708' or file == 'best_1690329462' or 'checkpoint' in file:
            continue
        print(file)
        # 执行信息抽取
        rules = json.load(open("../data/rules.json", "r", encoding="utf-8"))
        json.dump(rules, open("cache/exp1_2_input.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
        knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
        tco = token_classification(rules, knowledge, "../model/ours/" + file, "../data/tc_data.dict")
        json.dump(tco, open("cache/exp1_2_output.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
        # 整合预测与真实值
        integrate_tc("../data/rules.json", "cache/exp1_2_output.json", "cache/exp1_2_compare.log")
        # 评估
        evaluate("cache/exp1_2_compare.log", "cache/exp1_2_result.log", threshold=0.6)
    # # 执行信息抽取
    # rules = json.load(open("../data/rules.json", "r", encoding="utf-8"))
    # json.dump(rules, open("cache/exp1_2_input.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    # tco = token_classification(rules, "../data/knowledge.json", "../model/ours/best_1690329462", "../data/tc_data.dict")
    # json.dump(rules, open("cache/exp1_2_output.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    # # 整合预测与真实值
    # integrate_tc("../data/rules.json", "cache/exp1_2_output.json", "cache/exp1_2_compare.log")
    # # 评估
    # evaluate("cache/exp1_2_compare.log", "cache/exp1_2_result.log", threshold=0.6)
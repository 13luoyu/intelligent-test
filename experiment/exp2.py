# 生成规则，并比较数目和质量
# 质量的比较比较松

from ours.process_tco_to_r1 import to_r1
from transfer.mydsl_to_rules import read_file

def compute_BR_num(BR_file, out_file):
    with open(BR_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    count = 0
    for line in lines:
        if "if" in line:
            count += 1
    with open(out_file, "w", encoding="utf-8") as f:
        f.write(f"总计规则数：{count}\n")
    print(f"规则数：{count}")



def edit_distance(s1, s2):
    """
    衡量两个字符串的相似度，计算两个字符串的编辑距离。编辑距离指的是将一个字符串转换成另一个字符串所需的最少操作次数，包括插入、删除、替换操作。
    """
    len1, len2 = len(s1), len(s2)
    dp = [[0] * (len2+1) for _ in range(len1+1)]
    for i in range(len1+1):
        dp[i][0] = i
    for j in range(len2+1):
        dp[0][j] = j
    for i in range(1, len1+1):
        for j in range(1, len2+1):
            if s1[i-1] == s2[j-1]:
                dp[i][j] = dp[i-1][j-1]
            else:
                dp[i][j] = min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1]) + 1
    return dp[len1][len2]


def str_same(s1, s2, rate = 0.2):
    # s1是预测值，s2是真实值
    distance = edit_distance(s1, s2)
    if float(distance) / float(len(s2)) < rate:
        return True
    else:
        return False


def compute_BR_precision(our_file, correct_file, out_file):
    _, _, our_rules = read_file(our_file)
    _, _, correct_rules = read_file(correct_file)
    a, b = 0, 0
    total, correct = [], []
    # 将同一id的所有约束去重地混合在一起，然后比较是否缺失，是否正确
    ckeys, okeys = list(correct_rules.keys()), list(our_rules.keys())
    while a < len(ckeys):
        cconstraints, oconstraints = [], []
        crule_id = ckeys[a].split("_")[0] if "_" in ckeys[a] else ".".join(ckeys[a].split(".")[:-1])

        while a < len(ckeys) and ckeys[a].find(crule_id) == 0:
            # 将约束增加到cconstraints中
            crule = correct_rules[ckeys[a]]
            for c in crule["constraints"] + crule["results"]:
                if c not in cconstraints:
                    cconstraints.append(c)
            a = a + 1
        
        while b < len(okeys) and okeys[b].find(crule_id) == 0:
            # 将约束增加到oconstraints中
            orule = our_rules[okeys[b]]
            for c in orule["constraints"] + orule["results"]:
                if c not in oconstraints:
                    oconstraints.append(c)
            b = b + 1
        # 比较cconstraints中的每个元素，oconstraints中是否有，是否正确，正确的话count+1
        count = 0
        total.append(len(cconstraints))
        for cc in cconstraints:
            for oc in oconstraints:
                if str_same(cc["key"], oc["key"]) and str_same(cc["value"], oc["value"]):
                    count += 1
                    break
        correct.append(count)
    
    
    print(f"约束数目：{sum(total)}，其中正确的数目：{sum(correct)}，正确率：{round(float(sum(correct))/float(sum(total)), 3)}")
    with open(out_file, "a", encoding="utf-8") as f:
        f.write(f"约束数目：{sum(total)}，其中正确的数目：{sum(correct)}，正确率：{round(float(sum(correct))/float(sum(total)), 3)}")







if __name__ == "__main__":
    # 生成BR
    # to_r1("data/exp1_2_output.json", "data/exp1_3_r1.mydsl", "../data/knowledge.json")
    to_r1("../data/rules.json", "data/exp1_3_correct.mydsl", "../data/knowledge.json")
    # 计算BR的数目
    # compute_BR_num("data/exp1_3_r1.mydsl", "data/exp1_3_result.log")
    # 将BR中的约束子句提取出来，并与正确的用例比较，看准确率是多少
    # compute_BR_precision("data/exp1_3_r1.mydsl", "data/exp1_3_correct.mydsl", "data/exp1_3_result.log")
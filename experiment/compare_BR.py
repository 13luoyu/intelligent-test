import nltk
import pprint

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



def read_llm_result(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    rules = []
    ids = []
    dataset_index = []
    constraints = []
    next_id = False
    for x, line in enumerate(lines):
        if ("sage" in file and x < 79) or ("claude" in file and x < 125) or ("chatgpt" in file and x < 88):  # 忽略开头的提示部分
            continue
        l = line.strip().split()
        if next_id:
            if "." in l[0] or ("第" in l[0] and "条" in l[0]):
                rule_id = l[0]
                ids.append(rule_id)
            next_id = False
            continue
        if len(l) == 0:
            continue
        if "数据集" in l[0]:
            dataset_index.append(len(ids))
        elif l[0] == "Q":
            if len(constraints) > 0:
                rules.append(constraints)
            elif len(ids) > 0:
                ids.pop()
            constraints = []
            next_id = True
        elif l[0] == "if":
            i = 1
            while i < len(l):
                constraint = dict()
                
                next_and = i + 1
                while next_and < len(l) and l[next_and] != "and":
                    next_and += 1
                if next_and - i == 3:
                    constraint["key"] = l[i]
                    if l[i] == "单笔最大申报数量":
                        constraint["key"] = "申报数量"
                        l[i] = "申报数量"
                    constraint["value"] = l[i + 2]
                    if constraint["value"][0] == "\"":
                        constraint["value"] = constraint["value"][1:]
                    if constraint["value"][-1] == "\"":
                        constraint["value"] = constraint["value"][:-1]
                    if l[i+1] != "is":
                        constraint["value"] = str(l[i+1]) + str(l[i + 2][1:-1])
                    if constraint not in constraints:
                        constraints.append(constraint)
                    i = i + 4
                elif next_and - i == 2:
                    constraint["key"] = l[i]
                    constraint["value"] = l[i+1]
                    if constraint["value"][0] == "\"":
                        constraint["value"] = constraint["value"][1:]
                    if constraint["value"][-1] == "\"":
                        constraint["value"] = constraint["value"][:-1]
                    if constraint not in constraints:
                        constraints.append(constraint)
                    i = i + 3
                else:
                    i += 1
        elif l[0] == "then":
            i = 1
            while i < len(l):
                result = dict()
                next_and = i + 1
                while next_and < len(l) and l[next_and] != "and":
                    next_and += 1
                if next_and - i == 3:
                    result["key"] = l[i]
                    result["value"] = l[i + 2]
                    if result["value"][0] == "\"":
                        result["value"] = result["value"][1:]
                    if result["value"][-1] == "\"":
                        result["value"] = result["value"][:-1]

                    if "不" in result["value"]:  # 默认result["key"][0] == "不"
                        result["else"] = result["value"][1:]
                    else: # then 结果 is "成功"
                        result["else"] = "不" + result["value"]
                    if result not in constraints:
                        constraints.append(result)
                    i += 4
                elif next_and - i == 2:
                    result["key"] = l[i]
                    result["value"] = l[i + 1]
                    if result["value"][0] == "\"":
                        result["value"] = result["value"][1:]
                    if result["value"][-1] == "\"":
                        result["value"] = result["value"][:-1]
                    if "不" in result["value"]:  # 默认result["key"][0] == "不"
                        result["else"] = result["value"][1:]
                    else: # then 结果 is "成功"
                        result["else"] = "不" + result["value"]
                    if result not in constraints:
                        constraints.append(result)
                    i += 3
                else:
                    i += 1
    if len(constraints) > 0:
        rules.append(constraints)
    elif len(ids) > 0:
        ids.pop()
    dataset_index.append(len(ids))
    dataset_index = [0] + dataset_index
    return ids, rules, dataset_index


def read_correct_rules(correct_file):
    with open(correct_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    rules = []
    ids = []
    dataset_index = []
    constraints = []
    last_rule_id = ""
    for line in lines:
        l = line.strip().split()
        if len(l) == 0:
            continue
        if "dataset" in l[0]:
            dataset_index.append(len(ids))
        elif l[0] == "rule":
            rule_id = l[1]
            if "_" in rule_id:
                rule_id = rule_id.split("_")[0]
            else:
                rule_id = ".".join(rule_id.split(".")[:-1])
            if rule_id != last_rule_id:
                if last_rule_id != "":
                    rules.append(constraints)
                    constraints = []
                ids.append(rule_id)
                last_rule_id = rule_id
        elif l[0] == "if":
            i = 1
            while i < len(l):
                constraint = {}
                constraint["key"] = l[i]
                if l[i] == "单笔最大申报数量":
                    constraint["key"] = "申报数量"
                    l[i] = "申报数量"
                constraint["value"] = l[i + 2][1:-1]
                if l[i+1] != "is":
                    constraint["value"] = str(l[i+1]) + str(l[i + 2][1:-1])
                i = i + 4
                if constraint not in constraints:
                    constraints.append(constraint)
        elif l[0] == "then":
            i = 1
            while i < len(l):
                result = {}
                result["key"] = l[i]
                result["value"] = l[i+2][1:-1]
                if "不" in result["value"]:  # 默认result["key"][0] == "不"
                    result["else"] = result["value"][1:]
                else: # then 结果 is "成功"
                    result["else"] = "不" + result["value"]
                i += 4
                if result not in constraints:
                    constraints.append(result)
    if len(constraints) > 0:
        rules.append(constraints)
    dataset_index.append(len(ids))
    return ids, rules, dataset_index



def read_our_rules(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    rules = []
    ids = []
    constraints = []
    last_rule_id = ""
    for line in lines:
        l = line.strip().split()
        if len(l) == 0:
            continue
        if l[0] == "rule":
            if "_" in l[1]:
                rule_id = l[1].split("_")[0]
            else:
                rule_id = '.'.join(l[1].split(".")[:-1])
            if rule_id != last_rule_id:
                if last_rule_id != "":
                    rules.append(constraints)
                    constraints = []
                ids.append(rule_id)
                last_rule_id = rule_id
        elif l[0] == "if":
            i = 1
            while i < len(l):
                constraint = dict()
                
                constraint["key"] = l[i]
                if l[i] == "单笔最大申报数量":
                    constraint["key"] = "申报数量"
                    l[i] = "申报数量"
                constraint["value"] = l[i + 2][1:-1]
                if l[i+1] != "is":
                    constraint["value"] = str(l[i+1]) + str(l[i + 2][1:-1])
                if constraint not in constraints:
                    constraints.append(constraint)
                i = i + 4
        elif l[0] == "then":
            i = 1
            while i < len(l):
                result = dict()
                result["key"] = l[i]
                result["value"] = l[i + 2][1:-1]
                if "不" in result["value"]:  # 默认result["key"][0] == "不"
                    result["else"] = result["value"][1:]
                else: # then 结果 is "成功"
                    result["else"] = "不" + result["value"]
                if result not in constraints:
                    constraints.append(result)
                i += 4
    
    rules.append(constraints)
    return ids, rules


def read_1_3_llm_file(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    rules = []
    ids = []
    constraints = []
    last_rule_id = ""
    for line in lines:
        l = line.strip().split()
        if len(l) == 0:
            continue
        if l[0] == "rule":
            if "_" in l[1]:
                rule_id = l[1].split("_")[0]
            else:
                rule_id = '.'.join(l[1].split(".")[:-1])
            if rule_id != last_rule_id:
                if last_rule_id != "":
                    rules.append(constraints)
                    constraints = []
                ids.append(rule_id)
                last_rule_id = rule_id
        elif l[0] == "if":
            i = 1
            while i < len(l):
                constraint = dict()
                
                next_and = i + 1
                while next_and < len(l) and l[next_and] != "and":
                    next_and += 1
                if next_and - i == 3:
                    constraint["key"] = l[i]
                    if l[i] == "单笔最大申报数量":
                        constraint["key"] = "申报数量"
                        l[i] = "申报数量"
                    constraint["value"] = l[i + 2]
                    if constraint["value"][0] == "\"":
                        constraint["value"] = constraint["value"][1:]
                    
                    if constraint["value"][-1] == "\"":
                        constraint["value"] = constraint["value"][:-1]
                    if l[i+1] != "is":
                        constraint["value"] = str(l[i+1]) + str(l[i + 2][1:-1])
                    if constraint not in constraints:
                        constraints.append(constraint)
                    i = i + 4
                elif next_and - i == 2:
                    constraint["key"] = l[i]
                    constraint["value"] = l[i+1]
                    if constraint["value"][0] == "\"":
                        constraint["value"] = constraint["value"][1:]
                    if constraint["value"][-1] == "\"":
                        constraint["value"] = constraint["value"][:-1]
                    if constraint not in constraints:
                        constraints.append(constraint)
                    i = i + 3
                else:
                    i += 1
        elif l[0] == "then":
            i = 1
            while i < len(l):
                result = dict()
                next_and = i + 1
                while next_and < len(l) and l[next_and] != "and":
                    next_and += 1
                if next_and - i == 3:
                    result["key"] = l[i]
                    result["value"] = l[i + 2]
                    if result["value"][0] == "\"":
                        result["value"] = result["value"][1:]
                    if result["value"][-1] == "\"":
                        result["value"] = result["value"][:-1]

                    if "不" in result["value"]:  # 默认result["key"][0] == "不"
                        result["else"] = result["value"][1:]
                    else: # then 结果 is "成功"
                        result["else"] = "不" + result["value"]
                    if result not in constraints:
                        constraints.append(result)
                    i += 4
                elif next_and - i == 2:
                    result["key"] = l[i]
                    result["value"] = l[i + 1]
                    if result["value"][0] == "\"":
                        result["value"] = result["value"][1:]
                    if result["value"][-1] == "\"":
                        result["value"] = result["value"][:-1]
                    if "不" in result["value"]:  # 默认result["key"][0] == "不"
                        result["else"] = result["value"][1:]
                    else: # then 结果 is "成功"
                        result["else"] = "不" + result["value"]
                    if result not in constraints:
                        constraints.append(result)
                    i += 3
                else:
                    i += 1
    
    rules.append(constraints)
    return ids, rules


# 思路是这样的：
# 对于一条自然语言规则，假设对于correct，它的if和then中有6个要素，对于other，它有3个要素，那么
# 计算正确率时，正确率=正确要素数/6，
# 如果某个标签具有多个取值，那么按比例计算，比如某标签可以取值a、b，测试用例中只有a，那么这里的要素数=0.5
def compute_BR_precision(our_file, correct_file, fp):
    if "exp1_3" in our_file:
        correct_ids, correct_rules= read_our_rules(correct_file)
        if "sage" in our_file or "claude" in our_file or "chatgpt" in our_file:
            our_ids, our_rules= read_1_3_llm_file(our_file)
            our = list(zip(our_ids, our_rules))
            our = sorted(our, key=lambda x:x[0])
            our_ids, our_rules = [xi[0] for xi in our], [xi[1] for xi in our]
            correct = list(zip(correct_ids, correct_rules))
            correct = sorted(correct, key = lambda x:x[0])
            correct_ids, correct_rules = [xi[0] for xi in correct], [xi[1] for xi in correct]
        else:
            our_ids, our_rules = read_our_rules(our_file)
        correct_indexs = [0]
    elif "exp2" in our_file:
        if "sage" in our_file or "claude" in our_file or "chatgpt" in our_file:
            our_ids, our_rules, our_indexs = read_llm_result(our_file)
        else:
            our_ids, our_rules, _ = read_correct_rules(our_file)
        correct_ids, correct_rules, correct_indexs = read_correct_rules(correct_file)

    a, b = 0, 0
    total, correct = [], []
    # print(len(correct_ids), len(correct_rules))
    # print(len(our_ids), len(our_rules))
    # exit(0)
    # 将同一id的所有约束去重地混合在一起，然后比较是否缺失，是否正确
    last_b = 0
    while a < len(correct_rules):
        c_id = correct_ids[a]
        cconstraints = correct_rules[a]
        last_b = b
        find = False
        while b < len(our_rules):
            o_id = our_ids[b]
            oconstraints = our_rules[b]
            if o_id == c_id:
                find = True
                break
            b += 1
        if not find:
            b = last_b
        
        # cconstraints = sorted(cconstraints, key=lambda a:a["key"])
        # oconstraints = sorted(oconstraints, key=lambda a:a["key"])
        # 比较cconstraints中的每个元素，oconstraints中是否有，是否正确，正确的话count+1
        count = 0
        total.append(len(cconstraints))
        for cc in cconstraints:
            for oc in oconstraints:
                if str_same(cc["key"], oc["key"], 0.6) and str_same(cc["value"], oc["value"], 0.6):
                    count += 1
                    break
        correct.append(count)
        a += 1
        if a in correct_indexs:  # 一个数据集的结束
            index = correct_indexs.index(a)
            c_num = sum(total[correct_indexs[index-1]:correct_indexs[index]])
            co_num = sum(correct[correct_indexs[index-1]:correct_indexs[index]])
            rate = round(float(co_num) / float(c_num), 4)
            print(f"数据集{index}，约束数目：{c_num}，正确数目：{co_num}，正确率：{rate}")
            fp.write(f"数据集{index}，约束数目：{c_num}，正确数目：{co_num}，正确率：{rate}\n")
    
    # 全部
    print(f"总约束数目：{sum(total)}，其中正确的数目：{sum(correct)}，正确率：{round(float(sum(correct))/float(sum(total)), 4)}")
    fp.write(f"总约束数目：{sum(total)}，其中正确的数目：{sum(correct)}，正确率：{round(float(sum(correct))/float(sum(total)), 4)}")



def compute_BR_num(BR_file, fp):
    with open(BR_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    index = 0
    count = 0
    for line in lines:
        if "数据集" in line or "dataset" in line:
            if index > 0:
                print(f"数据集{index}，规则数{count}")
                fp.write(f"数据集{index}，规则数{count}\n")
            index += 1
            count = 0
        elif "if" in line:
            count += 1
    print(f"数据集{index}，规则数{count}")
    fp.write(f"数据集{index}，规则数{count}\n")
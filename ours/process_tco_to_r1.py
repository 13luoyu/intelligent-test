import json
from collections import OrderedDict
import copy
from pprint import pprint


def is_time_key(key):
    if "时" in key or "点" in key or "日" in key:
        return True
    return False

def is_num_key(key):
    if "量" in key or "数" in key:
        return True
    return False

def is_price_key(key):
    if "价" in key or "基准" == key:
        return True
    return False

def judge_compose(op1, op2):
    if ("买入" in op1 or "卖出" in op1) and ("申报" in op2 or "撤销" in op2):
        return True, op2 + op1
    elif ("申报" in op1 or "撤销" in op1) and ("买入" in op2 or "卖出" in op2):
        return True, op1 + op2
    else:
        return False, ""


def read_knowledges(file):
    knowledge = json.load(open(file, "r", encoding="utf-8"))
    return knowledge


def read_OBI_to_rule(texts, labels):
    """
    读取模型输出的OBI文件，将其转化为key-value对的形式，存放在stack中。同时记录句子中的；和。并记录在sentence_separate_1和sentence_separate_2中

    :param texts: 一段自然语言
    :param labels: texts对应的标签序列，以空格分隔的字符串形式呈现
    :return stack: 按照出现顺序记录text-label对的数组
    :return sentence_separate_1: 记录；之后的下一个{label:text}在stack中的位置
    :return sentence_separate_2: 记录。之后的下一个{label:text}在stack中的位置
    """
    stack = []  # 按顺序记录所有的label及其对应text为{label:text}
    sentence_separate_1 = []  # 记录；之后的下一个{label:text}在stack中的位置
    sentence_separate_2 = []  # 记录。之后的下一个{label:text}在stack中的位置
    sentence_separate_3 = []  # 记录，之后的下一个{label:text}在stack中的位置
    sentence_and = []  # 记录"且"之后的下一个{label:text}在stack中的位置
    a, b = 0, 0  # a, b为一个text在句子中的开始和结束位置
    last_label = "O"
    for i, label in enumerate(labels.split(" ")):
        if label == "O":  # O->O, B->O, I->O
            if last_label != "O":  # B->O, I->O
                b = i
                # 记录到stack中
                stack.append({last_label: texts[a:b]})
            last_label = label
        else:
            l_content = label[2:]
            if "B" == label[0]:  # O->B，I->B，B->B
                # 处理旧标签
                if last_label != "O":
                    b = i
                    # 记录到stack中
                    stack.append({last_label: texts[a:b]})
                # 记录新标签
                a = i
                last_label = l_content
            else:  # 如果是... -> I
                ...
        if texts[i] == "；":
            sentence_separate_1.append(len(stack))  # 记录；之后的下一个{label:text}在stack中的位置
        elif texts[i] == "。":
            sentence_separate_2.append(len(stack))  # 记录。之后的下一个{label:text}在stack中的位置
        elif texts[i] == "，":
            sentence_separate_3.append(len(stack))  # 记录，之后的下一个{label:text}在stack中的位置
        elif texts[i] == "且":
            sentence_and.append(len(stack))
    sentence_separate_2.pop()  # 句子的结尾一定是。而这个。无用
    return stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and


def separate_rule_to_subrule(stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and):
    """
    将stack中的内容分成多个子规则

    :param stack: 按照出现顺序记录text-label对的数组
    :param sentence_separate_1: 记录；之后的下一个{label:text}在stack中的位置
    :param sentence_separate_2: 记录。之后的下一个{label:text}在stack中的位置
    :return ss: 子规则数组，每个数组元素为一个子规则，子规则形式上为包含一系列key-value对的字典。
    """
    # pprint(stack)
    # print(sentence_separate_1)
    # print(sentence_separate_2)
    ss = []
    last_or = False
    ss.append([])  # 按照插入的顺序排列键-值对
    ss_now = 0  # 每次后面出现新的key，它的对应key-value会被添加到ss[ss_now:]的所有字典中
    for cnt, kv in enumerate(stack):
        key = list(kv.keys())[0]
        value = kv[key]
        # 如果上一个句子以句号结尾，直接分裂并更新ss_now，表示后面的规则和前面无关
        if cnt in sentence_separate_2:
            new_rule = []
            new_rule.append({key:value})
            ss_now = len(ss)
            ss.append(new_rule)
            continue
        # 如果遇到or，分裂，但不更新ss_now，表示后面的规则和前面有关
        if key == "or":
            new_rule = []
            # 将除了or对应的键之外的所有key-value对复制
            for k in ss[-1][:-1]:
                new_rule.append(k)
            ss.append(new_rule)
            last_or = True
            continue
        if_add = False  # 判断当前的key-value是否被添加到了某一个规则中，如果没有，就说明出现了冲突，需要分裂
        for s in ss[ss_now:]:
            find = False
            for i, si in enumerate(s):
                if list(si.keys())[0] == key:
                    find = True
                    find_value = si[key]
                    break
            if find:
                # 前面写了{交易品种:债券}，后面出现了{交易品种:债券现券}的情况，这里后面要写的更通用 TODO
                if key == "交易品种":  
                    if find_value == "债券":
                        del s[i]
                        s.append({key:value})
                        if_add = True
                elif key == "数量":  # 如果是数量约束，可能是一条规则中对数量有多条约束
                    if last_or:
                        last_or = False
                        ss[-1].append({key:value})
                        if_add = True
                        break
                    elif cnt in sentence_and:  # 对数量多条约束
                        s[i][key] += ","+value
                        if_add = True
                    else:
                        # 特殊处理，卖出时不足10万元面额部分，一次性申报
                        # 创建新规则
                        new_rule = []
                        # 复制上一条规则的每个字段，直到遇见冲突
                        for i, k in enumerate(ss[-1]):
                            if list(k.keys())[0] == key:
                                break
                            new_rule.append(k)
                        # 找到>i的最小的新标点开始
                        min_index = len(stack)
                        for index in sentence_separate_1 + sentence_separate_2 + sentence_separate_3:
                            if index <= cnt - (len(ss[-1]) - i):
                                continue
                            min_index = min(min_index, index)
                        # 将min_index之后的测试点都从ss[-1]移到new_rule上
                        # print(stack[min_index])
                        tk = list(stack[min_index].keys())[0]
                        for i, k in enumerate(ss[-1]):
                            if list(k.keys())[0] == tk:
                                break
                        for j, k in enumerate(ss[-1][i:]):
                            new_rule.append(k)
                            del ss[-1][j+i]
                        # 更新ss_now，之后只更新new_rule，前面的不再更新
                        ss_now = len(ss)
                        new_rule.append({key:value})  # 将新的数量-value写入new_rule
                        ss.append(new_rule)
                        if_add = True  # 不冲突，无需分裂
                        break
                elif key == "操作":
                    # 有些操作可以合并
                    op1 = value
                    op2 = find_value
                    can_compose, op = judge_compose(op1, op2)  # 一次性申报卖出
                    if can_compose:
                        del s[i]
                        s.append({key:op})
                        if_add = True
                        break
                elif key == "key":
                    if_add = True
                    s.append({key:value})
                elif key == "价格":
                    if_add = True
                    if last_or:
                        last_or = False
                        ss[-1].append({key:value})
                        break
                    else:
                        s.append({key:value})
                elif key == "时间":
                    if_add = True
                    if last_or:
                        last_or = False
                        ss[-1].append({key:value})
                        break
                    else:
                        s.append({key:value})
            else:  # 一条规则中没有找到key，就添加进去
                s.append({key:value})
                if_add = True
        if not if_add or cnt in sentence_separate_1:  # 出现了冲突，分裂成两个规则
            if cnt in sentence_separate_1:  # 上一个句子以分号结尾，更新ss_now，表示之前的规则不再修改和添加key-value
                ss_now = len(ss)
            new_rule = []
            # 复制上一条规则的每个字段，直到遇见冲突
            for k in ss[-1]:
                if list(k.keys())[0] == key:
                    break
                new_rule.append(k)
            new_rule.append({key:value})
            ss.append(new_rule)
    return ss

def write_r1(fp_r1, ss, knowledge, id):
    """
    将ss中的所有子规则写成R1

    :param fp_r1 R1的文件符指针
    :param ss: 子规则数组
    :param knowledge: 领域知识
    :param id: 当前所有子规则的基准id
    """
    # pprint(ss)
    # 现在ss中存储了每一条规则，这里将其写成R1
    for i, s in enumerate(ss):
        key_to_use = {}
        value_to_use = {}
        op_to_use = ""
        new_id = id + "." + str(i+1)
        r1 = "if "
        focus = ""
        result = "成功"
        for i, si in enumerate(s):
            key = list(si.keys())[0]
            value = si[key]
            if key == "操作":
                focus = "订单连续性操作"
            if key == "结果":
                result = value
                continue
            if key not in ["时间", "价格", "数量", "key", "value", "op"]:
                r1 += f"{key} is \"{value}\" and "
            elif key == "op":
                op_to_use = value
            elif key == "时间":
                if focus != "订单连续性操作":
                    focus = "时间"
                if not key_to_use:  # 为空
                    if value_to_use:
                        v1 = list(value_to_use.keys())[0]
                        v2 = value_to_use[v1]
                        if v1 != "value":
                            op = "is"
                            if op_to_use != "":
                                op = op_to_use
                                op_to_use = ""
                            r1 += f"{v1} {op} \"{v2}\" and "
                        else:
                            r1 += f"约束 is \"v2\" and "
                    value_to_use = {key:value}
                else:
                    k1 = list(key_to_use.keys())[0]
                    v1 = key_to_use[k1]
                    if is_time_key(v1):
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        r1 += f"{v1} {op} \"{value}\" and "
                    else:
                        if value_to_use:
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            if v1 != "value":
                                op = "is"
                                if op_to_use != "":
                                    op = op_to_use
                                    op_to_use = ""
                                r1 += f"{v1} {op} \"{v2}\" and "
                            else:
                                r1 += f"约束 is \"v2\" and "
                        value_to_use = {key:value}
                    key_to_use = {}
            elif key == "价格":
                if focus != "订单连续性操作":
                    focus = "价格"
                if not key_to_use:  # 为空
                    if value_to_use:
                        v1 = list(value_to_use.keys())[0]
                        v2 = value_to_use[v1]
                        if v1 != "value":
                            op = "is"
                            if op_to_use != "":
                                op = op_to_use
                                op_to_use = ""
                            r1 += f"{v1} {op} \"{v2}\" and "
                        else:
                            r1 += f"约束 is \"v2\" and "
                    value_to_use = {key:value}
                else:
                    k1 = list(key_to_use.keys())[0]
                    v1 = key_to_use[k1]
                    if is_price_key(v1):
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        r1 += f"{v1} {op} \"{value}\" and "
                    else:
                        if value_to_use:
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            if v1 != "value":
                                op = "is"
                                if op_to_use != "":
                                    op = op_to_use
                                    op_to_use = ""
                                r1 += f"{v1} {op} \"{v2}\" and "
                            else:
                                r1 += f"约束 is \"v2\" and "
                        value_to_use = {key:value}
                    key_to_use = {}
            elif key == "数量":
                if focus != "订单连续性操作":
                    focus = "数量"
                if not key_to_use:  # 为空
                    if value_to_use:
                        v1 = list(value_to_use.keys())[0]
                        v2 = value_to_use[v1]
                        if v1 != "value":
                            op = "is"
                            if op_to_use != "":
                                op = op_to_use
                                op_to_use = ""
                            r1 += f"{v1} {op} \"{v2}\" and "
                        else:
                            r1 += f"约束 is \"v2\" and "
                    value_to_use = {key:value}
                else:
                    k1 = list(key_to_use.keys())[0]
                    v1 = key_to_use[k1]
                    if is_num_key(v1):
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        r1 += f"{v1} {op} \"{value}\" and "
                    else:
                        if value_to_use:
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            if v1 != "value":
                                op = "is"
                                if op_to_use != "":
                                    op = op_to_use
                                    op_to_use = ""
                                r1 += f"{v1} {op} \"{v2}\" and "
                            else:
                                r1 += f"约束 is \"v2\" and "
                        value_to_use = {key:value}
                    key_to_use = {}
            elif key == "key":
                if not value_to_use:  # 空，当前读到的key没有对应的value
                    key_to_use = {key:value}  # {"key":"开盘集合匹配时间"}
                else:
                    v1 = list(value_to_use.keys())[0]
                    v2 = value_to_use[v1]
                    if v1 == "时间":
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        if is_time_key(value):
                            r1 += f"{value} {op} \"{v2}\" and "
                        else:
                            r1 += f"{v1} {op} \"{v2}\" and "
                            key_to_use = {key:value}
                        value_to_use = {}
                    elif v1 == "数量":
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        if is_num_key(value):
                            r1 += f"{value} {op} \"{v2}\" and "
                        else:
                            r1 += f"{v1} {op} \"{v2}\" and "
                            key_to_use = {key:value}
                        value_to_use = {}
                    elif v1 == "价格":
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        if is_price_key(value):
                            r1 += f"{value} {op} \"{v2}\" and "
                        else:
                            r1 += f"{v1} {op} \"{v2}\" and "
                            key_to_use = {key:value}
                        value_to_use = {}
                    else:  # v1 == "value"，查找领域知识判断是否配对
                        find = False
                        for key_to_find in list(knowledge.keys()):
                            if key_to_find == key:
                                value_to_find = knowledge[key_to_find]
                                if isinstance(value_to_find, list):
                                    if v2 in value_to_find:
                                        find = True
                                        break
                        if find:
                            r1 += f"{value} is \"{v2}\" and "
                            value_to_use = {}
                        else:
                            r1 += f"约束 is \"{v2}\" and "
                            value_to_use = {}
                            key_to_use = {key:value}
            else:  # value
                # 在领域知识中寻找value
                find = False
                for key_to_find in list(knowledge.keys()):
                    value_to_find = knowledge[key_to_find]
                    if isinstance(value_to_find, list):
                        for v_to_find in value_to_find:
                            if v_to_find == value:
                                r1 += f"{key_to_find} is \"{value}\" and "
                                find = True
                                break
                    if find:
                        break
                if not find:
                    # 查看key_to_use看是否配对
                    if key_to_use:
                        k1 = list(key_to_use.keys())[0]
                        v1 = key_to_use[k1]
                        配对 = True  # TODO，在领域知识中找不到时，key-value是否配对
                        op = "is"
                        if op_to_use != "":
                            op = op_to_use
                            op_to_use = ""
                        if 配对:
                            r1 += f"{v1} {op} \"{value}\" and "
                            key_to_use = {}
                            find = True
                    if not find:
                        if value_to_use:
                            # 如果value_to_use不为空
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            op = "is"
                            if op_to_use != "":
                                op = op_to_use
                                op_to_use = ""
                            if v1 != "value":
                                r1 += f"{v1} {op} \"{v2}\" and "
                            else:
                                r1 += f"约束 is \"{v2}\" and "
                        value_to_use = {key: value}

        if value_to_use:
            v1 = list(value_to_use.keys())[0]
            v2 = value_to_use[v1]
            op = "is"
            if op_to_use != "":
                op = op_to_use
                op_to_use = ""
            if v1 == "时间" or v1 == "数量" or v1 == "价格":
                r1 += f"{v1} {op} \"{v2}\" and "
            else:
                r1 += f"约束 is \"{v2}\" and "
        
        fp_r1.write("rule " + new_id + "\n")
        fp_r1.write(f"focus: {focus}\n")
        fp_r1.write(f"\t{r1[:-5]}\n")
        fp_r1.write(f"\tthen 结果 is \"{result}\"\n")
        fp_r1.write(f"\n")




def to_r1(input_file, output_file, knowledge_file):
    """
    将input_file文件的内容写成R1，存放在output_file文件中
    :param input_file: 一个json文件，存放一或多篇文档中的按照id分好的自然语言text及其标签label
    :param output_file: 写R1的文件
    :param knowledge_file: 存储领域知识的文件
    """
    fp_r1 = open(output_file, "w", encoding="utf-8")
    knowledge = read_knowledges(knowledge_file)
    rules = json.load(open(input_file, "r", encoding="utf-8"))
    for rule in rules:
        id = rule["id"]
        texts = rule["text"]
        labels = rule["label"]
        
        stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and = read_OBI_to_rule(texts, labels)

        ss = separate_rule_to_subrule(stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and)
        
        write_r1(fp_r1, ss, knowledge, id)

    fp_r1.close()




if __name__ == "__main__":
    to_r1("rules_深圳证券交易所债券交易规则.json", "r1.mydsl", "../data/knowledge.json")
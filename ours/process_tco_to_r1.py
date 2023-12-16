import json
from collections import OrderedDict
import copy
import pprint
import os
import re

# 做法是在分规则后进行一步处理，依据原文中的关键字处理两个操作人。两个操作人的情况总共以上三种，向（与、给）、作为与无关。在第一步处理模型结果时要找到这个关系，传给第二步。

def is_time_key(key):
    if key[-1] == "日" or key[-2:] == "时间":
        return True
    return False

def is_num_key(key):
    if "量" in key or "数" in key:
        return True
    return False

def is_price_key(key):
    if ("价" in key or "基准" == key or "金额" in key) and "要素" not in key and "指令" not in key and "类型" not in key and "方式" not in key:
        return True
    return False

def judge_operation_compose(op1, op2):
    if ("买入" in op1 or "卖出" in op1 or "合并" in op1) and ("申报" in op2 or "撤销" in op2):
        return True, op2 + op1
    elif ("申报" in op1 or "撤销" in op1) and ("买入" in op2 or "卖出" in op2 or "合并" in op2):
        return True, op1 + op2
    else:
        return False, ""

def judge_operation_in(op1, op2):
    if op1 in op2 and "不" not in op2:
        return True, op2
    elif op2 in op1 and "不" not in op1:
        return True, op1
    else:
        return False, ""

def judge_time_compose(time1, time2):
    return True
    time1_cnt = len(re.findall(r"\d+:\d+", time1))
    time2_cnt = len(re.findall(r"\d+:\d+", time2))
    if time1_cnt > 0 and time2_cnt == 0 or time2_cnt > 0 and time1_cnt == 0:
        return True
    return False

def judge_tradetype_compose(t1, t2):
    if t1 == "债券" and ("债券现券" in t2 or "债券通用质押式回购" in t2):
        return True, t2
    if t1 == "证券" and t2 != "证券":
        return True, t2
    if t2 == "债券" and ("债券现券" in t1 or "债券通用质押式回购" in t1):
        return True, t1
    if t2== "证券" and t1 != "证券":
        return True, t1
    if t1 in t2:
        return True, t2
    if t2 in t1:
        return True, t1
    return False, ""



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
    sentence_and = []  # 记录"且"、"但"之后的下一个{label:text}在stack中的位置
    operator_relation = []  # 0 无关，1 向（给），2 与，3 作为，记录所有向（与，作为）操作人的信息
    a, b = 0, 0  # a, b为一个text在句子中的开始和结束位置
    last_label = "O"
    operator_count = 0
    for i, label in enumerate(labels.split(" ")):
        if label == "O":  # O->O, B->O, I->O
            if last_label != "O":  # B->O, I->O
                b = i
                # 记录到stack中
                stack.append({last_label: texts[a:b]})
                if last_label == "操作人":
                    operator_count += 1
                    if a == 0:
                        ...
                    elif texts[a-1] == "向" or texts[a-1] == "给" or (a-2 >= 0 and texts[a-2] == "委" and texts[a-1] == "托"):
                        operator_relation.append(1)
                    elif texts[a-1] == "与":
                        operator_relation.append(2)
                    elif a-2 >= 0 and texts[a-2] == "作" and texts[a-1] == "为":
                        operator_relation.append(3)
                    elif operator_count >= 2 and texts[a-1] == "，":
                        operator_relation.append(0)
            last_label = label
        else:
            l_content = label[2:]
            if "B" == label[0]:  # O->B，I->B，B->B
                # 处理旧标签
                if last_label != "O":
                    b = i
                    # 记录到stack中
                    stack.append({last_label: texts[a:b]})
                    if last_label == "操作人":
                        operator_count += 1
                        if a == 0:
                            ...
                        elif texts[a-1] == "向" or texts[a-1] == "给" or (a-2 >= 0 and texts[a-2] == "委" and texts[a-1] == "托"):
                            operator_relation.append(1)
                        elif texts[a-1] == "与":
                            operator_relation.append(2)
                        elif a-2 >= 0 and texts[a-2] == "作" and texts[a-1] == "为":
                            operator_relation.append(3)
                        elif operator_count >= 2 and texts[a-1] == "，":
                            operator_relation.append(0)
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
        elif texts[i] == "且" or texts[i] == "但":
            sentence_and.append(len(stack))
    sentence_separate_2.pop()  # 句子的结尾一定是。而这个。无用
    
    # 将stack中的申报类型显式点出 TODO
    # for i, s in enumerate(stack):
    #     key, value = list(s.keys())[0], s[list(s.keys())[0]]
    #     if len(value) >= 4 and value[-2:] == "申报" and "性" not in value:
    #         stack[i] = {"申报类型":value}

    # with open("rules_cache/r1_step1.txt", "a", encoding="utf-8") as f:
    #     f.write(f"输入：{texts}\n")
    #     f.write("输出:\n")
    #     f.write(pprint.pformat(stack) + "\n\n")
    
    return stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and, operator_relation


def separate_rule_to_subrule(stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and, operator_relation):
    """
    将stack中的内容分成多个子规则

    :param stack: 按照出现顺序记录text-label对的数组
    :param sentence_separate_1: 记录；之后的下一个{label:text}在stack中的位置
    :param sentence_separate_2: 记录。之后的下一个{label:text}在stack中的位置
    :return ss: 子规则数组，每个数组元素为一个子规则，子规则形式上为包含一系列key-value对的字典。
    """
    # pprint.pprint(stack)
    # print(sentence_separate_1)
    # print(sentence_separate_2)
    ss = []
    last_or = 0
    fan = 0
    ss.append([])  # 按照插入的顺序排列键-值对
    ss_now = 0  # 每次后面出现新的key，它的对应key-value会被添加到ss[ss_now:]的所有字典中
    for cnt, kv in enumerate(stack):
        key = list(kv.keys())[0]
        value = kv[key]
        # 如果上一个句子以句号或分号结尾，直接分裂并更新ss_now，表示后面的规则和前面无关
        if cnt in sentence_separate_2:
            new_rule = []
            new_rule.append({key:value})
            ss_now = len(ss)
            ss.append(new_rule)
            continue
        if cnt in sentence_separate_1:
            ss_now = len(ss)
            new_rule = []
            # 复制上一条规则的每个字段，直到遇见冲突
            for k in ss[-1]:
                if list(k.keys())[0] == key:
                    break
                new_rule.append(k)
            new_rule.append({key:value})
            ss.append(new_rule)
            continue
        # 如果遇到or，分裂，但不更新ss_now，表示后面的规则和前面有关
        if key == "or":
            new_rules = []
            for rule_to_cp in ss[ss_now:]:
                new_rule = []
                # 将除了or对应的键之外的所有key-value对复制
                # 如果or对应的键是操作、操作部分，则不复制这两个
                # 如果or对应的是key、op、value，则不复制这三个
                if len(rule_to_cp) > 1 and cnt+2 < len(stack) and ((list(rule_to_cp[-2].keys())[0] == "操作" and list(rule_to_cp[-1].keys())[0] == "操作部分") or (list(rule_to_cp[-1].keys())[0] == "操作" and list(rule_to_cp[-2].keys())[0] == "操作部分")) and (list(stack[cnt+1].keys())[0] == "操作" and list(stack[cnt+2].keys())[0] == "操作部分" or list(stack[cnt+1].keys())[0] == "操作部分" and list(stack[cnt+2].keys())[0] == "操作"):
                    for k in rule_to_cp[:-2]:
                        new_rule.append(k)
                    last_or = 2
                elif len(rule_to_cp) > 2 and cnt+3 < len(stack) and (list(rule_to_cp[-3].keys())[0] == "key" and list(rule_to_cp[-2].keys())[0] == "op" and (is_num_key(list(rule_to_cp[-1].keys())[0]) or is_price_key(list(rule_to_cp[-1].keys())[0]))) and (list(stack[cnt+1].keys())[0] == "key" and list(stack[cnt+2].keys())[0] == "op" and (is_num_key(list(stack[cnt+3].keys())[0]) or is_price_key(list(stack[cnt+3].keys())[0]))):
                    if "不" in rule_to_cp[-2]['op']:
                        rule_to_cp[-2]['op'] = rule_to_cp[-2]['op'][rule_to_cp[-2]['op'].find("不")+1:]
                    else:
                        rule_to_cp[-2]['op'] = "不" + rule_to_cp[-2]['op']
                    fan += 1
                    continue
                elif len(rule_to_cp) > 0 and cnt+1 < len(stack) and list(rule_to_cp[-1].keys())[0] == "交易方式" and list(stack[cnt+1].keys())[0] == "交易方式":
                    for k in rule_to_cp[:-1]:
                        new_rule.append(k)
                else:
                    for k in rule_to_cp[:-1]:
                        new_rule.append(k)
                    last_or = 1
                new_rules.append(new_rule)
            ss += new_rules
            continue
        if fan > 0:
            # 将所有结果改为不成功
            for rule in ss[ss_now:]:
                find = False
                for kv_ in rule:
                    key_ = list(kv_.keys())[0]
                    value_ = kv_[key_]
                    if key_ == "结果":
                        kv_[key_] = "不成功"
                        find = True
                if not find:
                    rule.insert(0, {"结果":"不成功"})
        if_add = False  # 判断当前的key-value是否被添加到了某一个规则中，如果没有，就说明出现了冲突，需要分裂
        for s in ss[ss_now:]:
            find = False
            for i, si in enumerate(s):
                if list(si.keys())[0] == key:
                    find = True
                    find_value = si[key]
                    break
            if find or fan > 0:
                if key == "交易品种":  
                    replace, v = judge_tradetype_compose(find_value, value)
                    if replace:
                        del s[i]
                        s.append({key:v})
                        if_add = True
                    else:
                        ...  # 冲突
                elif key == "数量":  # 如果是数量约束，可能是一条规则中对数量有多条约束
                    if fan > 0:
                        fan -= 1
                        s.append({key:value})
                        if_add = True
                        continue
                    special = False
                    for k in ss[-1]:
                        if "一次性" in k[list(k.keys())[0]]:
                            special = True
                    if last_or > 0:
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        if_add = True
                        break
                    elif cnt in sentence_and:  # 对数量多条约束
                        s[i][key] += ","+value
                        if_add = True
                    elif special:
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
                    else:
                        # 如果读到一个数量时，上面的数量不是数值，则不冲突
                        for si in s[::-1]:
                            ki = list(si.keys())[0]
                            vi = si[ki]
                            if ki == "数量":
                                if len(re.findall(r"\d+.\d+", vi)) == 0:
                                    s.append({key:value})
                                    if_add = True
                elif key == "操作":
                    if last_or > 0:
                        last_or = last_or - 1
                        rule_num = len(ss[ss_now:])
                        for ii, si in enumerate(ss[int(ss_now + rule_num/2):]):
                            si.append({key:value})
                        if_add = True
                        break
                    # 合并操作
                    op1 = value
                    op2 = find_value
                    can_compose, op = judge_operation_compose(op1, op2)  # 一次性申报卖出
                    if can_compose:
                        del s[i]
                        s.append({key:op})
                        if_add = True
                        break
                    # 操作是同一个
                    if_in, op = judge_operation_in(op1, op2)
                    if if_in:
                        del s[i]
                        s.append({key:op})
                        if_add = True
                        break
                    # 操作之间不冲突
                    s.append({key:value})
                    if_add = True
                elif key == "操作部分":
                    # 操作部分有时不冲突，有时隶属于一个操作，有时两个
                    if last_or > 0:
                        last_or = last_or - 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        if_add = True
                        break
                    else:
                        # 操作部分不冲突
                        s.append({key:value})
                        if_add = True
                        ...
                elif key == "操作人":
                    if_add = True
                    if last_or > 0:
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        break
                    else:
                        if 0 in operator_relation and cnt in sentence_separate_3:
                            new_rule = []
                            for k in ss[-1]:
                                if list(k.keys())[0] == key:
                                    break
                                new_rule.append(k)
                            new_rule.append({key:value})
                            ss_now = len(ss)
                            ss.append(new_rule)
                        else:
                            s.append({key:value})
                elif key == "结合规则":
                    if_add = True
                    find_state = False
                    for si in s:
                        if list(si.keys())[0] == key:
                            si[key] += "," + value
                            find_state = True
                    if not find_state:
                        s.append({key:value})
                elif key == "状态":
                    if_add = True
                    find_state = False
                    for si in s:
                        if list(si.keys())[0] == key:
                            si[key] += "," + value
                            find_state = True
                    if not find_state:
                        s.append({key:value})
                    ss_now = len(ss)-1
                    break
                elif key == "事件":
                    if_add = True
                    find_state = False
                    for si in s:
                        if list(si.keys())[0] == key:
                            si[key] += "," + value
                            find_state = True
                    if not find_state:
                        s.append({key:value})
                    ss_now = len(ss)-1
                    break
                elif key == "key":
                    if last_or > 0:
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        if_add = True
                        break
                    else:
                        # 如果两个key相同，则要分裂
                        find_conflict = False
                        for si in s:
                            if list(si.keys())[0] == key and si[key] == value:
                                # 冲突
                                find_conflict = True
                                break
                        if not find_conflict:
                            # key不冲突
                            s.append({key:value})
                            if_add = True
                            
                elif key == "价格":
                    if fan > 0:
                        fan -= 1
                        s.append({key:value})
                        if_add = True
                        continue
                    if last_or > 0:
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        if_add = True
                        break
                    else:
                        for si in s[::-1]:
                            ki = list(si.keys())[0]
                            vi = si[ki]
                            if ki == "价格":
                                if len(re.findall(r"\d+.\d+", vi)) == 0:
                                    s.append({key:value})
                                    if_add = True
                        # s.append({key:value})
                        # if_add = True
                elif key == "时间":
                    if last_or > 0:
                        if_add = True
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        break
                    else:
                        # 判断拆不拆，方法是如果一个是具体时间，一个是日期，则不拆，否则拆
                        time1 = s[i][key]
                        time2 = value
                        if judge_time_compose(time1, time2):
                            s.append({key:value})
                            if_add = True
                elif key == "系统":
                    if last_or > 0:
                        if_add = True
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        break
                    else:
                        s[i][key] = value
                        if_add = True
                elif key == "value":
                    if last_or > 0:
                        if_add = True
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        break
                    else:
                        for rule_to_add in ss[ss_now:]:
                            rule_to_add.append({key:value})
                        if_add = True
                elif key == "结果":
                    if value == "除外":
                        # 处理“...情况怎么样，...情况除外”
                        # 首先找到“除外”所在的短句
                        for sepi, sep in enumerate(sentence_separate_3):
                            if sepi + 1 < len(sentence_separate_3) and sep <= cnt and sentence_separate_3[sepi+1] > cnt:
                                break
                        # 找到其中的约束
                        cons = []
                        for con in stack[sep:]:
                            if "value" in con or "时间" in con or "数量" in con or "价格" in con or "交易方式" in con:
                                cons.append(con)
                        # 新增规则，“除外”的内容结果反过来，这里先记录
                        rules_to_add = []
                        for s in ss[ss_now:]:
                            rule_to_add = copy.deepcopy(s)
                            rules_to_add.append(rule_to_add)
                        # 修改“除外”的内容为非，或直接删掉（如果重复）
                        for s in ss[ss_now:]:
                            to_del = []
                            for sii, si in enumerate(s):
                                if si in cons:
                                    keyi = list(si.keys())[0]
                                    # 和前面重复，直接删掉
                                    cf = False
                                    for sj in s[:sii]:
                                        if keyi in sj:
                                            to_del.append(sii)
                                            cf = True
                                            break
                                    if not cf:
                                        si[keyi] = "非" + si[keyi]
                            for ind in reversed(to_del):
                                s.pop(ind)
                        # 依据除外新增规则
                        for s in rules_to_add:
                            to_del = []
                            has_rs = False
                            for sii, si in enumerate(s):
                                # 反转结果
                                if "结果" in si:
                                    if "不" in si["结果"] or si["结果"] == "无效":
                                        si["结果"] = "成功"
                                    else:
                                        si["结果"] = "不成功"
                                    has_rs = True
                                    continue
                                if si in cons:
                                    keyi = list(si.keys())[0]
                                    # 和前面重复，直接删掉前面的
                                    for sj in s[:sii]:
                                        if keyi in sj:
                                            to_del.append(sj)
                            for ind in to_del:
                                s.remove(ind)
                            if not has_rs:
                                s.append({"结果":"不成功"})
                        ss += rules_to_add
                        if_add = True
                        break
                elif key == "op":
                    if fan > 0:
                        if "不" in value:
                            value = value[value.find("不")+1:]
                        else:
                            value = "不" + value
                        s.append({key:value})
                        if_add = True
                        continue
                    if last_or > 0:
                        last_or -= 1
                        rule_num = len(ss[ss_now:])
                        for rule_to_add in ss[int(ss_now + rule_num/2):]:
                            rule_to_add.append({key:value})
                        if_add = True
                        break
                    s.append({key:value})
                    if_add = True
            else:  # 一条规则中没有找到key，就添加进去
                s.append({key:value})
                if_add = True
        if not if_add:  # 出现了冲突，分裂成两个规则
            # new_rule = []
            # # 复制上一条规则的每个字段，直到遇见冲突
            # for k in ss[-1]:
            #     if list(k.keys())[0] == key:
            #         break
            #     new_rule.append(k)
            # new：复制ss_now直到最后的每个字段，直到遇见冲突
            new_rule = []
            new_rules = []
            for s in ss[ss_now:]:
                for k in s:
                    if list(k.keys())[0] == key:
                        break
                    new_rule.append(k)
                new_rule.append({key:value})
                if new_rule not in new_rules:
                    new_rules.append(new_rule)
                new_rule = []
            
            ss += new_rules
    
    # 依据operator_relation处理操作人
    operator_index = 0
    use_index = False
    for s_index, s in enumerate(ss):
        # 如果s和上一个s不相似，则更新operator_index
        if use_index and s_index > 0:
            l1, l2 = len(s), len(ss[s_index-1])
            if l1 != l2:
                operator_index += 1
                use_index = False
        operator_count = 0
        for si in s:
            key = list(si.keys())[0]
            value = si[key]
            if key == "操作人":
                operator_count += 1
                if operator_count % 2 == 0 and operator_index in operator_relation:
                    if operator_relation[operator_index] == 1:
                        del si[key]
                        si["操作对象"] = value
                    elif operator_relation[operator_index] == 2:
                        del si[key]
                        si["关联操作人"] = value
                    elif operator_relation[operator_index] == 3:
                        del si[key]
                        si["操作角色"] = value
                    use_index = True
    # with open("rules_cache/r1_step2.txt", "a", encoding="utf-8") as f:
    #     f.write(pprint.pformat(ss) + "\n\n")
    return ss

def write_r1(fp_r1, ss, knowledge, id):
    """
    将ss中的所有子规则写成R1

    :param fp_r1 一个结果字符串
    :param ss: 子规则数组
    :param knowledge: 领域知识
    :param id: 当前所有子规则的基准id
    """
    # pprint.pprint(ss)
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
                            r1 += f"约束 is \"{v2}\" and "
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
                                r1 += f"约束 is \"{v2}\" and "
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
                            r1 += f"约束 is \"{v2}\" and "
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
                                r1 += f"约束 is \"{v2}\" and "
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
                            r1 += f"约束 is \"{v2}\" and "
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
                                r1 += f"约束 is \"{v2}\" and "
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
                            if "前" in op or "后" in op:
                                r1 += f"{v1} {op} \"{v2}\" and "
                            else:
                                r1 += f"{v1} is \"{v2}\" and "
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
                        if "其他" in value:
                            k = value[2:]
                            if k == key_to_find:
                                r1 += f"{key_to_find} is \"{value}\" and "
                                find = True
                                break
                        else:
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
        
        if focus == "":
            focus = "订单连续性操作"
        fp_r1 += "rule " + new_id + "\n"
        fp_r1 += f"sourceId {id}\n"
        fp_r1 += f"focus: {focus}\n"
        fp_r1 += f"\t{r1[:-5]}\n"
        fp_r1 += f"\tthen 结果 is \"{result}\"\n"
        fp_r1 += f"\n"
    return fp_r1




def to_r1(rules, knowledge):
    """
    将input_file文件的内容写成R1，存放在output_file文件中
    """
    if os.path.exists("rules_cache/r1_step1.txt"):
        os.remove("rules_cache/r1_step1.txt")
    if os.path.exists("rules_cache/r1_step2.txt"):
        os.remove("rules_cache/r1_step2.txt")
    unknown_id = 0
    r1 = ''
    for rule in rules:
        if 'id' in rule:
            id = rule["id"]
        else:
            id = str(unknown_id)
            unknown_id += 1
        texts = rule["text"]
        labels = rule["label"]
        
        stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and, operator_relation = read_OBI_to_rule(texts, labels)

        ss = separate_rule_to_subrule(stack, sentence_separate_1, sentence_separate_2, sentence_separate_3, sentence_and, operator_relation)
        
        r1 = write_r1(r1, ss, knowledge, id)
    return r1




if __name__ == "__main__":
    rules = json.load(open("rules_cache/tco.json", "r", encoding="utf-8"))
    knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    r1 = to_r1(rules, knowledge)
    with open("rules_cache/r1.mydsl", "w", encoding="utf-8") as f:
        f.write(r1)
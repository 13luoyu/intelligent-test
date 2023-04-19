import json
from collections import OrderedDict
import copy


def is_time_key(key):
    if "时" in key or "点" in key or "日" in key:
        return True
    return False

def is_num_key(key):
    if "量" in key or "数" in key:
        return True
    return False

def is_price_key(key):
    if "价" in key:
        return True
    return False


def read_knowledges(file):
    knowledge = json.load(open(file, "r", encoding="utf-8"))
    return knowledge

def to_r1(file, knowledge_file):
    fp_r1 = open('r1', "w", encoding="utf-8")

    knowledge = read_knowledges(knowledge_file)
    rules = json.load(open(file, "r", encoding="utf-8"))
    for rule in rules:
        id = rule["id"]
        text = rule["text"]
        label = rule["label"]
        stack = []  # 存储已有的label
        sentence_separate_1 = []  # ；
        sentence_separate_2 = []  # 。
        a, b = 0, 0
        last_label = "O"
        for i, l in enumerate(label.split(" ")):
            if l == "O":  # O->O, B->O, I->O
                if last_label != "O":  # B->O, I->O
                    b = i
                    # 记录到stack中
                    stack.append({last_label: text[a:b]})
                last_label = l
            else:
                l_content = l[2:]
                if "B" == l[0]:  # O->B，I->B，B->B
                    # 处理旧标签
                    if last_label != "O":
                        b = i
                        # 记录到stack中
                        stack.append({last_label: text[a:b]})
                    # 记录新标签
                    a = i
                    last_label = l_content
                else:  # 如果是... -> I
                    ...
            if text[i] == "；":
                sentence_separate_1.append(len(stack))
            elif text[i] == "。":
                sentence_separate_2.append(len(stack))
        sentence_separate_2.pop()

        
        # 将stack中的内容分成多个子句
        ss = [OrderedDict()]
        ss_now = 0
        for cnt, kv in enumerate(stack):
            key = list(kv.keys())[0]
            value = kv[key]
            # 如果上一个句子以句号结尾，直接分裂
            if cnt in sentence_separate_2:
                new_rule = OrderedDict()
                new_rule[key] = value
                ss_now = len(ss)
                ss.append(new_rule)
                continue
            # 如果遇到or，分裂
            if key == "or":
                new_rule = OrderedDict()
                for k in list(ss[-1].keys())[:-1]:
                    if k == key:
                        break
                    new_rule[k] = ss[-1][k]
                # new_rule[key] = value
                ss.append(new_rule)
                continue
            if_add = False
            for s in ss[ss_now:]:
                if key in list(s.keys()):
                    if key == "交易品种":
                        if s[key] == "债券":
                            del s[key]
                            s[key] = value
                            if_add = True
                    elif key == "数量":
                        s[key] = s[key] + "," + value
                        if_add = True
                elif key not in list(s.keys()):
                    s[key] = value
                    if_add = True
            if not if_add or cnt in sentence_separate_1:  # 分裂成两个规则
                if cnt in sentence_separate_1:
                    ss_now = len(ss)
                new_rule = OrderedDict()
                for k in list(ss[-1].keys()):
                    if k == key:
                        break
                    new_rule[k] = ss[-1][k]
                new_rule[key] = value
                ss.append(new_rule)
        

        for i, s in enumerate(ss):
            key_to_use = {}
            value_to_use = {}
            new_id = id + "." + str(i+1)
            r1 = "if "
            focus = ""
            result = "成功"
            for i, key in enumerate(s):
                value = s[key]
                if key == "操作":
                    focus = "订单连续性操作"
                if key == "结果":
                    result = value
                    continue
                if key not in ["时间", "价格", "数量", "key", "value"]:
                    r1 += f"{key} is \"{value}\" and "
                elif key == "时间":
                    if focus != "订单连续性操作":
                        focus = "时间"
                    if not key_to_use:  # 为空
                        if value_to_use:
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            r1 += f"{v1} is \"{v2}\" and "
                        value_to_use = {key:value}
                    else:
                        k1 = list(key_to_use.keys())[0]
                        v1 = key_to_use[k1]
                        if is_time_key(v1):
                            r1 += f"{v1} is \"{value}\" and "
                        else:
                            if value_to_use:
                                v1 = list(value_to_use.keys())[0]
                                v2 = value_to_use[v1]
                                r1 += f"{v1} is \"{v2}\" and "
                            value_to_use = {key:value}
                elif key == "价格":
                    if focus != "订单连续性操作":
                        focus = "价格"
                    if not key_to_use:  # 为空
                        if value_to_use:
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            r1 += f"{v1} is \"{v2}\" and "
                        value_to_use = {key:value}
                    else:
                        k1 = list(key_to_use.keys())[0]
                        v1 = key_to_use[k1]
                        if is_price_key(v1):
                            r1 += f"{v1} is \"{value}\" and "
                        else:
                            if value_to_use:
                                v1 = list(value_to_use.keys())[0]
                                v2 = value_to_use[v1]
                                r1 += f"{v1} is \"{v2}\" and "
                            value_to_use = {key:value}
                elif key == "数量":
                    if focus != "订单连续性操作":
                        focus = "数量"
                    if not key_to_use:  # 为空
                        if value_to_use:
                            v1 = list(value_to_use.keys())[0]
                            v2 = value_to_use[v1]
                            r1 += f"{v1} is \"{v2}\" and "
                        value_to_use = {key:value}
                    else:
                        k1 = list(key_to_use.keys())[0]
                        v1 = key_to_use[k1]
                        if is_num_key(v1):
                            r1 += f"{v1} is \"{value}\" and "
                        else:
                            if value_to_use:
                                v1 = list(value_to_use.keys())[0]
                                v2 = value_to_use[v1]
                                r1 += f"{v1} is \"{v2}\" and "
                            value_to_use = {key:value}
                elif key == "key":
                    if not value_to_use:  # 空
                        key_to_use = {key:value}
                    else:
                        v1 = list(value_to_use.keys())[0]
                        v2 = value_to_use[v1]
                        if is_time_key(value) and v1 == "时间":
                            r1 += f"{value} is \"{v2}\" and "
                            value_to_use = {}
                        elif is_num_key(value) and v1 == "数量":
                            r1 += f"{value} is \"{v2}\" and "
                            value_to_use = {}
                        elif is_price_key(value) and v1 == "价格":
                            r1 += f"{value} is \"{v2}\" and "
                            value_to_use = {}
                        else:
                            r1 += f"{value} is \"{v2}\" and "
                            value_to_use = {}
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
                        value_to_use = {key: value}

            if value_to_use:
                v1 = list(value_to_use.keys())[0]
                v2 = value_to_use[v1]
                r1 += f"{v1} is {v2} and "
            
            fp_r1.write("rule " + new_id + "\n")
            fp_r1.write(f"focus: {focus}\n")
            fp_r1.write(f"\t{r1[:-5]}\n")
            fp_r1.write(f"\tthen 结果 is {result}\n")
            fp_r1.write(f"\n")


    fp_r1.close()



if __name__ == "__main__":
    to_r1("rules.json", "../data/knowledge.json")
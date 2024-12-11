import hanlp
import json
from transfer.knowledge_tree import encode_tree
from tqdm import tqdm
import cn2an

HanLP = hanlp.load(hanlp.pretrained.mtl.CLOSE_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_BASE_ZH)



# doc = HanLP('2021年HanLPv2.1为生产环境带来次世代最先进的多语种NLP技术。', tasks='sdp')
# print(doc)
# doc['sdp']字段代表语义依存图的数组格式，数组中第i个子数组代表第i个单词的语义依存关系，子数组中每个二元组的格式为[中心词的下标, 与中心词的语义依存关系]。每个单词的语义依存关系可能有零个、一个或多个（任意数量）。

def read_OBI_to_rule(text, label):
    keys, values = [], []
    key_begin, key_end = 0, 0
    last_label = "O"
    for i, l in enumerate(label.split(" ")):
        if l == "O":  # O->O, B->O, I->O
            if last_label != "O":
                key_end = i
                keys.append(last_label)
                values.append(text[key_begin:key_end])
            last_label = "O"
        else:
            l_content = l[2:]
            if l[0] == "B":  #O->B, B->B, I->B
                # 处理旧标签
                if last_label != "O":
                    key_end = i
                    keys.append(last_label)
                    values.append(text[key_begin:key_end])
                key_begin = i
                last_label = l_content
            else:  # B->I, I->I
                ...  # 什么也不用做
    return keys, values


def is_number(s):
    try:
        s = cn2an.cn2an(s)
        return True
    except ValueError:
        return False
    

def fix_token(keys, values, text, terms):
    # 解决多字问题
    for i, (key, value) in enumerate(zip(keys, values)):
        if key.find("的") == 0 or key.find(")") == 0 or key.find("）") == 0:
            key = key[1:]
        if value.find("的") == 0 or value.find("于") == 0 or value.find("以") == 0 or value.find("用") == 0 or value.find(")") == 0 or value.find("）")==0:
            value = value[1:]
        if value.find("的") == len(value)-1 and key != "状态" and key != "事件":
            value = value[:-1]
        if key.find("（") == len(key)-1 or key.find("(") == len(key)-1:
            key = key[:-1]
        if value.find("(") == len(value)-1 or value.find("（") == len(value)-1:
            value = value[:-1]
        
        if "(" in value and ")" in value:
            if value.find("(") < value.find(")"):
                cnt = value[value.find("(")+1:value.find(")")]
                if is_number(cnt):
                    value = value[value.find(")")+1:]
            else:
                value = value[value.find(")")+1:value.find("(")]
        if "（" in value and "）" in value:
            if value.find("（") < value.find("）"):
                cnt = value[value.find("（")+1:value.find("）")]
                if is_number(cnt):
                    value = value[value.find("）")+1:]
            else:
                value = value[value.find("）")+1:value.find("（")]

        keys[i] = key
        values[i] = value
    
    # 解决少字问题
    p=0
    for i, (key, value) in enumerate(zip(keys, values)):
        p = text.find(value, p)
        
        l = 0
        target_text = ""
        for term in terms:
            if value in term and term in text and len(term) > l:
                value_in_term_begin_index = term.find(value)
                if p - value_in_term_begin_index < 0 or text[p-value_in_term_begin_index:p-value_in_term_begin_index+len(term)] != term:
                    continue
                target_text = term
                l = len(term)
        if target_text != "":
            value = target_text

        if "交易方式" == value[-4:]:
            value = value[:-2]
        keys[i] = key
        values[i] = value
    
    return keys, values




def get_key_based_on_value(value, knowledge):
    knowledge = encode_tree(knowledge)
    for know in knowledge:
        content = know['content']
        k, v = content.split(":")
        if value == v:
            return k
    return None

def compose_kv(text, keys, values, knowledge):
    """使用语义依存分析结合算法进行key-value组合以及规则分割"""
    r1_kvs = []
    doc = HanLP(text, tasks='sdp')
    # print(doc)
    # print(doc.to_conll())
    tok, sdp = doc['tok/fine'], doc['sdp']
    # for i, (t, s) in enumerate(zip(tok, sdp)):
    #     words = [tok[si[0]-1] for si in s]
    #     print(i, t, s, words)
    # 1、一般，谓词是一个根节点，如果key-value最终以同一个谓词连接（具有相同的根节点），key-value组合
    # 2、如果有并列关系，将规则分割为子规则

    tok_index = 0  # 在遍历中tok_index和value保持同步的位置
    key_cache, value_cache = [], []  # key_cache=[(key, [parent_index])], value_cache=[(value_key, value, [parent_index])]
    op_cache = ""
    for key, value in zip(keys, values):
        while tok_index < len(tok) and tok[tok_index] not in value:
            tok_index += 1
        if key in ["key", "value", "时间", "数量", "价格"]:  # 需要组合的key-value对
            # 找到key/value在依存句法树中依赖的上级节点
            # 1.1 找到key/value中每个词依赖的上级节点
            parent_index = []
            begin_tok_index = tok_index
            while tok_index < len(tok) and tok[tok_index] in value:
                parent_index += [s[0]-1 for s in sdp[tok_index] if s[0] > 0]  # 这里-1很关键，因为sdp每个元素的索引i对应tok[i-1]
                tok_index += 1
            # 1.2 将自身内部各种依存关系的节点去掉，只保留外部关系
            parent_index = list(set(parent_index))
            for index in range(begin_tok_index, tok_index):  
                if index in parent_index:
                    parent_index.remove(index)
            # 1.3 剩下的就是key/value依赖的上级节点，加入cache中，最后一起匹配
            if key == "key":
                key_cache.append((value, parent_index))
            else:
                if op_cache:
                    value_cache.append((key, f"{op_cache}&{value}", parent_index))
                else:
                    value_cache.append((key, value, parent_index))
                op_cache = ""
        elif key == "op":
            op_cache = value.replace("得", "")
        else:  # 普通的键值对，直接组合
            while tok_index < len(tok) and tok[tok_index] in value:
                tok_index += 1
            r1_kvs.append((key, value))
    # print(key_cache, value_cache)

    # 1.4 匹配key/value的上级节点是否有相同的节点，如果有，组合成key-value；如果没有，标注为约束:key/value
    key_find, value_find = [False for _ in key_cache], [False for _ in value_cache]
    i, j = 0, 0
    while i < len(key_cache) and j < len(value_cache):
        key, l_key = key_cache[i]
        value_key, value, l_value = value_cache[j]
        if list(set(l_key) & set(l_value)):
            r1_kvs.append((key, value))
            key_find[i] = True
            value_find[j] = True
            i += 1
            j += 1
        elif i > 0:
            i -= 1
            if list(set(l_key) & set(l_value)):
                r1_kvs.append((key, value))
                value_find[j] = True
                i += 1
                j += 1
            else:
                j += 1
                i += 1
        else:
            j += 1
    i, j = 0, 0
    while i < len(key_cache) and j < len(value_cache):
        while i < len(key_cache) and key_find[i]:
            i += 1
        while j < len(value_cache) and value_find[j]:
            j += 1
        if i >= len(key_cache) or j >= len(value_cache):
            break
        key, l_key = key_cache[i]
        value_key, value, l_value = value_cache[j]
        key_pos = []
        pos=0
        while key in text[pos:]:
            pos = text.index(key, pos)
            key_pos.append(pos)
            pos += len(key)
        value_pos = []
        pos=0

        local_value = value
        if "&" in value:
            local_value = value.split("&")[1]
        while local_value in text[pos:]:
            pos = text.index(local_value, pos)
            value_pos.append(pos)
            pos += len(local_value)
        
        find = False
        for p1 in key_pos:
            for p2 in value_pos:
                if abs(p1 + len(key) - p2) <= 2 or abs(p2 + len(local_value) - p1) <= 2 or abs(p2+len(value.replace('&','')) - p1) <= 2:  # 考虑op
                    r1_kvs.append((key, value))
                    key_find[i] = True
                    value_find[j] = True
                    find = True
                    break
            if find:
                break
        if find:
            i += 1
            j += 1
        else:
            key = get_key_based_on_value(local_value, knowledge)
            if key != None:
                r1_kvs.append((key, value))
            else:
                if value_key == "value":
                    r1_kvs.append(("约束", value))
                else:
                    r1_kvs.append((value_key, value))
            value_find[j] = True
            j += 1
    j = 0
    while j < len(value_cache):
        if not value_find[j]:
            value_key, value, _ = value_cache[j]
            local_value = value
            if "&" in value:
                local_value = value.split("&")[1]
            key = get_key_based_on_value(local_value, knowledge)
            if key != None:
                r1_kvs.append((key, value))
            else:
                if value_key == "value":
                    r1_kvs.append(("约束", value))
                else:
                    r1_kvs.append((value_key, value))
        j += 1
    # 将r1_kvs按照在text中的位置排序
    new_r1_kvs = []
    kvs_pos = []
    for key, value in r1_kvs:
        local_value = value
        if "&" in value:
            local_value = value.split("&")[1]
        pos = values.index(local_value)
        while pos in kvs_pos:
            pos = values.index(local_value, pos+1)
        kvs_pos.append(pos)
    r1_kvs = sorted(list(zip(r1_kvs, kvs_pos)), key=lambda x: x[1])
    r1_kvs = [x[0] for x in r1_kvs]
    # print(r1_kvs)

    # # 将并列关系(eCoo)分割为子规则
    # # sdp标注了每个词对应的中心词。如果一个词和另一个词为并列关系，它们所有的子树的词应该被划分到不同的规则中，并列部分外的词应该都加到这些规则中。
    # # 2.1 寻找并列关系
    # eCoo = []
    # for i, (t, s) in enumerate(zip(tok, sdp)):
    #     for si in s:
    #         if si[1] == "eCoo":
    #             eCoo.append((i, si[0]-1))
    # # 2.2 寻找并列关系的子树
    # sub_rules = {}
    # eCoo_list = []
    # for i, j in eCoo:
    #     eCoo_list += [i, j]
    # eCoo_list = sorted(list(set(eCoo_list)))
    # for eCoo_i in eCoo_list:
    #     sub_rule = []
    #     q = [eCoo_i]
    #     idx = 0
    #     while idx < len(q):
    #         i = q[idx]
    #         idx += 1
    #         sub_rule.append(i)
    #         for j, sdpi in enumerate(sdp):  # 找到所有依赖i的词，加入q
    #             for si in sdpi:
    #                 if si[0]-1 == i and j not in q:
    #                     q.append(j)
    #     sub_rules[eCoo_i] = sorted(list(set(sub_rule)))
    
    # # HanLP识别的并列关系就是一坨屎，还是手动处理吧
    # # for key in sub_rules:
    # #     print(tok[key], [tok[i] for i in sub_rules[key]])


    # 2.1 按照。和；划分规则
    new_r1_kvs = [[]]
    add_index_now = 0
    last_pos, pos = -1, 0
    for key, value in r1_kvs:
        local_value = value
        if "&" in value:
            local_value = value.split("&")[1]
        pos = text.index(local_value, pos)
        if last_pos == -1:
            new_r1_kvs[add_index_now].append((key, value))
            last_pos = pos
        else:
            find = False
            for c in text[last_pos:pos]:
                if c in ["。", "；"]:
                    find = True
                    break
            if find:
                new_r1_kvs.append([])
                add_index_now = len(new_r1_kvs) - 1
                new_r1_kvs[add_index_now].append((key, value))
            else:
                new_r1_kvs[add_index_now].append((key, value))
            last_pos = pos
    r1_kvs = new_r1_kvs

    


    # 2.2 处理或关系
    # 或的内容可以是一个（交易方式、操作人），也可以是多个（操作-操作部分 or 操作-操作部分）
    new_r1_kvs = []
    for rule in r1_kvs:
        i = 0
        new_r1_kvs.append([])
        add_index_now = len(new_r1_kvs) - 1
        while i < len(rule):
            key, value = rule[i]
            if key == "or":
                if i - 2 >= 0 and i + 2 < len(rule) and (rule[i-2][0], rule[i-1][0]) in [("操作", "操作部分"), ("操作部分", "操作")] and (rule[i+1][0], rule[i+2][0]) in [("操作", "操作部分"), ("操作部分", "操作")]:
                    t = []
                    for new_rule in new_r1_kvs[add_index_now:]:
                        t.append(new_rule[:-2] + [rule[i+1], rule[i+2]])
                    new_r1_kvs += t
                    i += 3
                elif i - 1 >= 0 and i + 1 < len(rule):
                    t = []
                    for new_rule in new_r1_kvs[add_index_now:]:
                        t.append(new_rule[:-1] + [rule[i+1]])
                    new_r1_kvs += t
                    i += 2
                else:
                    i += 1
            else:
                for new_rule in new_r1_kvs[add_index_now:]:
                    new_rule.append((key, value))
                i += 1

    r1_kvs = new_r1_kvs

    # 2.3 如果遇到重复的，不是操作人、操作、操作部分、状态、事件、时间、数量、价格、约束、op、结果，就分割
    new_r1_kvs = []
    add_index_now = 0
    for r1_kv in r1_kvs:
        new_r1_kvs.append([])
        add_index_now = len(new_r1_kvs) - 1
        
        for key, value in r1_kv:
            find = False
            for idx, (k, v) in enumerate(new_r1_kvs[add_index_now]):
                if key == k:
                    find = True
                    break
            if find:
                if key in ["操作人", "操作", "操作部分", "状态", "事件", "时间", "数量", "价格", "约束", "op", "结果"]:
                    for rule in new_r1_kvs[add_index_now:]:
                        rule.append((key, value))
                else:  # 分割规则
                    t = []
                    for rule in new_r1_kvs[add_index_now:]:
                        t.append(rule[:idx] + [(key, value)])
                    new_r1_kvs += t
                    if idx == len(new_r1_kvs[add_index_now]) - 1:
                        # 不更新add_index_now，比如采用匹配成交、协商成交方式的，...
                        ...
                    else:
                        add_index_now = len(new_r1_kvs) - len(t)
            else:
                for rule in new_r1_kvs[add_index_now:]:
                    rule.append((key, value))
    r1_kvs = new_r1_kvs
    # print(r1_kvs)


    # 2.4 处理“结果 is 除外”，将除外的那句话单独提取出来作为一个规则
    new_r1_kvs = []
    for r1_kv in r1_kvs:
        find = False
        for i, (key, value) in enumerate(r1_kv):
            if "除外" in value:
                find = True
                break
        if not find:
            new_r1_kvs.append(r1_kv)
        else:
            except_index = text.index("除外")
            while except_index >= 0 and text[except_index] not in ["。", "，", "；"]:
                except_index -= 1
            except_index += 1
            except_text = text[except_index:]
            i = len(r1_kv)-2  # 一般表述为...除外，除外是r1_kv[-1]因此匹配从r1_kv[-2]开始匹配
            while i >= 0:
                if r1_kv[i][1] in except_text:
                    i -= 1
                else:
                    break
            new_r1_kvs.append(r1_kv[:i+1])
            new_r1_kvs.append(r1_kv)
    for rule in new_r1_kvs:
        result = []
        for i, (key, value) in enumerate(rule):
            if key == "结果":
                if value == "除外":
                    result.append(i)
                else:
                    if "不" in value:
                        rule[i] = (rule[i][0], "不成功")
                    else:
                        rule[i] = (rule[i][0], "成功")
                    result.append(i)
        if len(result) == 0:
            rule.append(("结果", "成功"))
        elif len(result) == 1:
            if rule[result[0]][1] == "除外":
                rule[result[0]] = (rule[result[0]][0], "不成功")
            else:
                ...
        else:
            del_index = -1
            for r in result:
                if rule[r][1] == "除外":
                    del_index = r
                    break
            if del_index != -1:
                for r in result:
                    if r != del_index:
                        rule[r] = (rule[r][0], "成功") if "不" in rule[r][1] else (rule[r][0], "不成功")
                del rule[del_index]

    r1_kvs = new_r1_kvs
    
    
    return r1_kvs

def digit_is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False

def compose_r1(id, kvs):
    r1 = ""
    index = 1
    for rule in kvs:
        focus = "订单连续性操作"
        for key, value in rule:
            if "时间" in key and ":" in value:
                key = "时间"
            elif "数量" in key and any(digit_is_number(c) for c in value):
                key = "数量"
            elif "价格" in key and any(digit_is_number(c) for c in value):
                key = "价格"

        tr = f"rule {id}.{index+1}\n"
        tr += f"sourceId {id}\n"
        tr += f"focus: {focus}\n"
        tr += "\tif "
        result = "成功"
        for key, value in rule:
            if key == "结果":
                result = "不成功" if "不" in value or "除外" in value else "成功"
            else:
                if "&" in value:
                    op, value = value.split("&")
                else:
                    op, value = "is", value
                tr += f"{key} {op} \"{value}\" and "
        tr = tr[:-5] + "\n"
        tr += f"\tthen 结果 is \"{result}\"\n"
        tr += "\n"
        cond = tr.split("if")[-1].split("then")[0].strip()
        if cond not in r1:
            r1 += tr
            index += 1
    return r1






def to_r1(rules, knowledge, terms):
    unknown_id = 0
    r1 = ""
    for rule in tqdm(rules):
        if "id" in rule:
            id = rule["id"]
        else:
            id = str(unknown_id)
            unknown_id += 1
        text = rule["text"]
        label = rule["label"]
        keys, values = read_OBI_to_rule(text, label)

        keys, values = fix_token(keys, values, text, terms)

        kvs = compose_kv(text, keys, values, knowledge)
        r1_local = compose_r1(id, kvs)
        r1 += r1_local
    return r1


if __name__ == "__main__":
    rules = json.load(open("cache/tco.json", "r", encoding="utf-8"))
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json", "r", encoding="utf-8"))
    terms = open("../data/domain_knowledge/terms.txt", "r", encoding="utf-8").read().split("\n")
    r1 = to_r1(rules, knowledge, terms)
    with open("cache/r1.mydsl", "w", encoding="utf-8") as f:
        f.write(r1)





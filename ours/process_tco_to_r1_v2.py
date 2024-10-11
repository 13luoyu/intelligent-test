import hanlp
import json

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


def compose_r1(text, keys, values):
    """语义依存分析"""
    r1_kvs = []
    doc = HanLP(text, tasks='sdp')
    # print(doc)
    tok, sdp = doc['tok/fine'], doc['sdp']
    # for i, (t, s) in enumerate(zip(tok, sdp)):
    #     words = [tok[si[0]-1] for si in s]
    #     print(i, t, s, words)
    # 1、一般，谓词是一个根节点，如果key-value最终以同一个谓词连接（具有相同的根节点），key-value组合
    # 2、如果有并列关系，将规则分割为子规则

    tok_index = 0  # 在遍历中tok_index和value保持同步的位置
    key_cache, value_cache = [], []
    for key, value in zip(keys, values):
        while tok[tok_index] not in value:
            tok_index += 1
        if key in ["key", "value", "时间", "数量", "价格"]:  # 需要组合的key-value对
            # 找到key/value在依存句法树中依赖的上级节点
            # 1.1 找到key/value中每个词依赖的上级节点
            parent_index = []
            begin_tok_index = tok_index
            while tok[tok_index] in value:
                parent_index += [s[0]-1 for s in sdp[tok_index]]  # 这里-1很关键，因为sdp每个元素的索引i对应tok[i-1]
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
                value_cache.append((value, parent_index))
        else:  # 普通的键值对，直接组合
            while tok[tok_index] in value:
                tok_index += 1
            r1_kvs.append((key, value))
    for key, l in key_cache:
        print(key, [(li, tok[li]) for li in l])
    for value, l in value_cache:
        print(value, [(li, tok[li]) for li in l])
    # 1.4 匹配key/value的上级节点是否有相同的节点，如果有，组合成key-value；如果没有，将key/value作为一个单独的key-value对




def to_r1(rules, knowledge):
    unknown_id = 0
    r1 = ""
    for rule in rules:
        if "id" in rule:
            id = rule["id"]
        else:
            id = str(unknown_id)
            unknown_id += 1
        text = rule["text"]
        label = rule["label"]
        keys, values = read_OBI_to_rule(text, label)
        r1_local = compose_r1(text, keys, values)
        exit(0)


if __name__ == "__main__":
    rules = json.load(open("cache/tco.json", "r", encoding="utf-8"))
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json", "r", encoding="utf-8"))
    r1 = to_r1(rules, knowledge)
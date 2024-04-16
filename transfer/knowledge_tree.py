import json
import copy


def encode_tree(knowledge):
    index, root_index = 1, None
    tree = []
    tree, index = encode(knowledge, tree, index, root_index)
    return tree

def encode(knowledge, tree, index, father_index):
    if knowledge == {}:
        return tree, index
    for key in list(knowledge.keys()):
        tree.append({"id":index, "content":key, "father_id":father_index})
        index += 1
        tree, index = encode(knowledge[key], tree, index, index - 1)
    return tree, index

# 例如：给定交易市场、交易品种，获取所有对应的交易方式
def get_constrainted_values(knowledge, defines, base_key):
    values = []
    if "交易市场" in defines and f"交易市场:{defines['交易市场'][0]}" in knowledge:
        knowledge = knowledge[f"交易市场:{defines['交易市场'][0]}"]
    if "交易品种" in defines:
        if f"交易品种:{defines['交易品种'][0]}" in knowledge:
            knowledge = knowledge[f"交易品种:{defines['交易品种'][0]}"]
        elif f"业务:{defines['交易品种'][0]}" in knowledge:
            knowledge = knowledge[f"业务:{defines['交易品种'][0]}"]
        else:
            queen = [knowledge]
            head, tail = 0, 0
            find_key = defines['交易品种'][0]
            find = False
            while head <= tail:
                for key in queen[head]:
                    if find_key == key.split(":")[-1]:
                        knowledge = queen[head][key]
                        find = True
                        break
                    else:
                        if queen[head][key] != {}:
                            queen.append(queen[head][key])
                            tail += 1
                if find:
                    break
                head += 1

    queen = [knowledge]
    head, tail = 0, 0
    find = False
    while head <= tail:
        for key in queen[head]:
            if base_key == key.split(":")[0]:
                values.append(key.split(":")[-1])
                find = True
            else:
                if queen[head][key] != {}:
                    queen.append(queen[head][key])
                    tail += 1
        if find:
            break
        head += 1

    return values

# 例如：给定交易市场、交易品种，（以及交易方式），获取所有子内容
def get_constrainted_all_subvalues(knowledge, defines, base_key=None):
    values = []
    varieties = []
    for key in encode_tree(knowledge):
        if "品种" in key['content'].split(":")[0] or "业务" == key['content'].split(":")[0]:
            varieties.append(key['content'].split(":")[-1])
    # 限制，避免过久的运行
    if "交易品种" not in defines or "交易市场" not in defines or defines["交易品种"][0] not in varieties:
        return values
    if "交易市场" in defines and f"交易市场:{defines['交易市场'][0]}" in knowledge:
        knowledge = knowledge[f"交易市场:{defines['交易市场'][0]}"]
    ori_knowledge = copy.deepcopy(knowledge)
    if "交易品种" in defines:
        if f"交易品种:{defines['交易品种'][0]}" in knowledge:
            knowledge = knowledge[f"交易品种:{defines['交易品种'][0]}"]
        elif f"业务:{defines['交易品种'][0]}" in knowledge:
            knowledge = knowledge[f"业务:{defines['交易品种'][0]}"]
        else:
            queen = [knowledge]
            head, tail = 0, 0
            find_key = defines['交易品种'][0]
            find = False
            while head <= tail:
                for key in queen[head]:
                    if find_key == key.split(":")[-1]:
                        knowledge = queen[head][key]
                        find = True
                        break
                    else:
                        if queen[head][key] != {}:
                            queen.append(queen[head][key])
                            tail += 1
                if find:
                    break
                head += 1
    
    if "交易方式" in defines:
        queen = [knowledge]
        head, tail = 0, 0
        find_key = defines['交易方式'][0]
        while head <= tail:
            to_del_key = []
            for key in queen[head]:
                if key.split(":")[0] == "交易方式" and key.split(":")[-1] != find_key:
                    to_del_key.append(key)
                else:
                    if queen[head][key] != {}:
                        queen.append(queen[head][key])
                        tail += 1
            for key in to_del_key:
                del queen[head][key]
            head += 1
        
    
    if base_key is not None:
        queen = [knowledge]
        head, tail = 0, 0
        find_key = defines['交易品种'][0]
        find = False
        while head <= tail:
            for key in queen[head]:
                if base_key == key.split(":")[-1]:
                    knowledge = queen[head][key]
                    find = True
                    break
                else:
                    if queen[head][key] != {}:
                        queen.append(queen[head][key])
                        tail += 1
            if find:
                break
            head += 1
        if not find:
            knowledge = {}
    # 提取 *品种，交易方式，以及一些特殊的知识
    want_key = ["指令", "要素", "品种", "交易方式", "申报类型", "价格类型", "申报方式", "成交方式", "结算方式", "竞买方式", "多主体中标方式"]
    
    knowledge = remove_extro_type(knowledge)

    # 限制，避免过久的运行
    if knowledge == ori_knowledge:
        return values

    # 寻找所有内容
    values = dfs(knowledge, want_key)

    return values

def remove_extro_type(knowledge):
    have_pz, have_fs = False, False
    for key in knowledge:
        if "品种" in key:
            have_pz = True
        if "交易方式" in key:
            have_fs = True
    if have_pz and have_fs:
        to_del_key = []
        for key in knowledge:
            if "品种" in key:
                fs = get_constrainted_values(knowledge, {key.split(":")[0]:key.split(":")[-1]}, "交易方式")
                if len(fs) > 0:
                    to_del_key.append(key)
        for key in to_del_key:
            del knowledge[key]
        return knowledge
    else:
        return knowledge


def dfs(knowledge, want_key):
    if knowledge == {}:
        return []
    elements = []
    element = []
    last_key = ""
    values = []
    for base_key in want_key:
        for key in knowledge:
            if base_key in key.split(":")[0]:
                if "指令" in base_key or "要素" in base_key:
                    if last_key != key.split(":")[0] and element != []:
                        if element not in elements:
                            elements.append(element)
                        element = []
                    element.append(key)
                    last_key = key.split(":")[0]
                else:
                    new_values = dfs(knowledge[key], want_key)
                    if len(new_values) == 0:
                        new_values = [[key]]
                    else:
                        new_values = [[key] + value for value in new_values]
                    values += new_values

        if element != []:
            if element not in elements:
                elements.append(element)
            element = []
            last_key = ""

    if values == []:
        value = []
        for element in elements:
            k, v = "", ""
            for e in element:
                k = e.split(":")[0]
                v = v + e.split(":")[-1] + ","
            v = v[:-1]
            value.append(f"{k}:{v}")
        values.append(value)
    else:
        # 笛卡尔组合
        values = merge(values)
        for value in values:
            for element in elements:
                k, v = "", ""
                for e in element:
                    k = e.split(":")[0]
                    v = v + e.split(":")[-1] + ","
                v = v[:-1]
                value.append(f"{k}:{v}")
    

    return values

def merge(values):
    new_values = []
    for index in range(1<<len(values)):
        new_value = []
        conflict = False
        for i, value in enumerate(values):
            if index & 1<<i > 0:
                if new_value == []:
                    for v in value:
                        new_value.append(v)
                else:
                    conflict = judge_conflict(new_value, value)
                    if conflict:
                        break
                    for v in value:
                        if v not in new_value:
                            new_value.append(v)
        if not conflict:
            new_values.append(new_value)
    
    # 去重
    values = sorted(new_values, key=lambda x:len(x))
    new_values = []
    while len(values)>0:
        new_values.append(values[-1])
        del values[-1]
        to_del_index = []
        for i, value in enumerate(values):
            exceed = False
            for v in value:
                if v not in new_values[-1]:
                    exceed = True
                    break
            if not exceed or value == []:
                to_del_index.append(i)
        to_del_index.reverse()
        for index in to_del_index:
            del values[index]

    return new_values

def judge_conflict(value1, value2):
    for v1 in value1:
        for v2 in value2:
            if v1.split(":")[0] == v2.split(":")[0] and v1.split(":")[1] != v2.split(":")[1]:
                return True
    return False


def decode_tree(knowledge_tree):
    knowledge = {}
    for k in knowledge_tree:
        key = f"{k['id']};{k['content']}"
        if k['father_id'] == None:
            knowledge[key] = {}
        else:
            _, knowledge = decode(knowledge, key, k['father_id'])
    
    knowledge = simplify(knowledge)
    return knowledge

def decode(knowledge, key, father_id):
    if knowledge == {}:
        return False, knowledge
    for k in list(knowledge.keys()):
        if str(father_id) == k.split(";")[0]:
            knowledge[k][key] = {}
            return True, knowledge
        if_add, knowledge[k] = decode(knowledge[k], key, father_id)
        if if_add:
            return True, knowledge
    return False, knowledge

def simplify(knowledge):
    if knowledge == {}:
        return knowledge
    for k in list(knowledge.keys()):
        new_k = k.split(";")[-1]
        knowledge[new_k] = knowledge[k]
        del knowledge[k]
        knowledge[new_k] = simplify(knowledge[new_k])
    return knowledge

if __name__ == "__main__":
    knowledge_file = "../data/domain_knowledge/classification_knowledge.json"
    knowledge_tree_file = "../data/domain_knowledge/classification_knowledge_tree.json"
    after_decode_file = "../data/domain_knowledge/classification_knowledge_decode.json"

    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    knowledge_tree = encode_tree(knowledge)
    json.dump(knowledge_tree, open(knowledge_tree_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    knowledge = decode_tree(knowledge_tree)
    json.dump(knowledge, open(after_decode_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # values = get_constrainted_values(knowledge, {"交易市场":["深圳证券交易所"], "交易品种":["债券"]}, "交易方式")
    values = get_constrainted_all_subvalues(knowledge, {"交易市场":["深圳证券交易所"], "交易品种":["可转债"]})
    # print(values)
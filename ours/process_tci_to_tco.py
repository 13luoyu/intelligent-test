# token classification任务

import json
from transformers import AutoModelForTokenClassification, AutoTokenizer
import torch
from utils.data_loader import read_dict
import hanlp
import re
from ours.process_r1_to_r2 import is_num_key, is_price_key
from utils.try_gpu import try_gpu


def change(begin, end, label, tag):
    index = begin
    if "状态" not in label[index] and "事件" not in label[index] and "操作人" not in label[index]:
        flag = 1
    else:
        flag = 0
    for index in range(begin, end):
        # 不是状态、事件
        if flag:
            if index == begin:
                label[index] = "B-" + tag
            else:
                label[index] = "I-" + tag
    return label

def lx(label, x, y):
    if x>0:
        l1 = label[x-1]
    else:
        return False
    for i in range(x, y, 1):
        if label[i]!=l1:
            return False
    if y < len(label):
        if label[y]!=l1:
            return False
    return True

def token_classification_with_algorithm(tco, knowledge):
    # 所有可以补的标签：
    # 交易品种、交易方式、结合规则、结果、系统、or、时间、价格、数量、op
    # 还需要将标签修复完整
    punctuation = [",", ";", "!", "?", "，", "。", "；", "！", "？", "为"]
    HanLP = hanlp.load(hanlp.pretrained.mtl.CLOSE_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_BASE_ZH)
    for ri, rule in enumerate(tco):
        text, label = rule["text"], rule["label"].split(" ")
        # 交易品种
        types = []
        for key in knowledge:
            if "品种" in key and isinstance(knowledge[key], list):
                types += knowledge[key]
            elif isinstance(knowledge[key], str) and knowledge[key][-2:] == "股票":
                types.append(key)
        # print(len(text), len(label))
        for t in types:
            p = text.find(t)
            while p != -1:
                label = change(p, p+len(t), label, "交易品种")
                p = text.find(t, p+len(t))
        p = text.find("单笔")
        while p != -1:
            label = change(p, p+2, label, "key")
            p = text.find("单笔", p+2)
                
        # 交易方式
        types = []
        for key in knowledge:
            if "交易方式" in key and isinstance(knowledge[key], list):
                types += knowledge[key]
            elif isinstance(knowledge[key], str) and "交易方式" == knowledge[key][-4:]:
                types.append(key)
        for t in types:
            p = text.find(t)
            while p != -1:
                if not lx(label, p, p+len(t)):
                    label = change(p, p+len(t), label, "交易方式")
                p = text.find(t, p+len(t))
        
        # 结合规则
        # 第..条，本规则第..条，《》，《》第..条
        p1 = text.find("《")
        p2 = text.find("》")
        p3 = text.find("第", p2+1)
        p4 = text.find("条", p2+1)

        while p1 != -1 and p2 != -1:
            if p3>0 and p4>0 and p3-p2<=2:
                label = change(p1, p4+1, label, "结合规则")
            else:
                label = change(p1, p2+1, label, "结合规则")
            p1 = text.find("《", p2+1)
            p2 = text.find("》", p2+1)
            p3 = text.find("第", p2+1)
            p4 = text.find("条", p2+1)

        p1 = text.find("本规则")
        p3 = text.find("第", p1+3)
        p4 = text.find("条", p1+3)
        while p1 != -1:
            if p3>0 and p4>0 and p3-p2<=2:
                label = change(p1, p4+1, label, "结合规则")
            p1 = text.find("本规则", p1+3)
            p3 = text.find("第", p1+3)
            p4 = text.find("条", p1+3)

        p1 = text.find("第")
        p2 = text.find("条")
        while p1 != -1 and p2 != -1:
            if "结合规则" in label[p1] and "结合规则" in label[p2]:
                break
            label = change(p1, p2+1, label, "结合规则")
            p1 = text.find("第", p2+1)
            p2 = text.find("条", p2+1)

        # 结果
        p = text.find("可以")
        while p != -1:
            label = change(p, p+2, label, "结果")
            p = text.find("可以", p+2)
        p = text.find("不得")
        while p != -1:
            label = change(p, p+2, label, "结果")
            p = text.find("不得", p+2)
        p = text.find("不接受")
        while p != -1:
            label = change(p, p+3, label, "结果")
            p = text.find("不接受", p+3)
        p = text.find("有效")
        while p != -1:
            label = change(p, p+2, label, "结果")
            p = text.find("有效", p+2)
        # 系统
        p = text.find("本所")
        while p != -1:
            label = change(p, p+2, label, "系统")
            p = text.find("本所", p+2)
        # or
        p = text.find("或")
        while p != -1:
            label = change(p, p+1, label, "or")
            p = text.find("或", p+1)
        p = text.find("或者")
        while p != -1:
            label = change(p, p+2, label, "or")
            p = text.find("或者", p+2)
        # op
        types = []
        for key in knowledge:
            if "本数" in key and isinstance(knowledge[key], list):
                types += knowledge[key]
        for t in types:
            p = text.find(t)
            # 这里修正的时候把“不...”的情况也考虑进去
            while p != -1:
                q = p
                if p-1 > 0 and text[p-1] == "不":  # 不少于
                    q = p-1
                elif p-2 > 0 and text[p-2] == "不":  # 不得少于
                    q = p-2
                elif p-3 > 0 and text[p-3] == "不":  # 不可以少于
                    q = p-3
                label = change(q, p+len(t), label, "op")
                p = text.find(t, p+len(t))

        # 操作
        operation = ["撤销","撤单","申报"]
        for op in operation:
            p = text.find(op)
            while p != -1:
                if label[p] == label[p+1] and label[p] == "O" or "操作" in label[p] and "操作部分" not in label[p] or "操作" in label[p+1] and "操作部分" not in label[p+1]:
                    label = change(p, p+2, label, "操作")
                p = text.find(op, p+2)
        # 操作部分
        p = text.find("申报")
        while p != -1:
            # 如果后面有撤销
            a, b = p, p+2
            while b<len(text) and text[b] not in punctuation:
                if text[b] == ":":
                    if text[b-1].isdigit() and text[b+1].isdigit():
                        b += 1
                    else:
                        break
                else:
                    b += 1
            if "撤" in text[a:b]:
                while a>0 and text[a] not in punctuation:
                    a -= 1
                a += 1
                label = change(a, p+2, label, "操作部分")
            p = text.find("申报", p+2)

        # 小修正，先分词，然后理论上同一组词应该具有相同的标签，如果连续不同的词具有相同的标签，应该是一个词
        
        doc = HanLP(text, tasks='srl')
        words = doc["tok/fine"]
        index = [0]
        i = 0
        for word in words:
            i += len(word)
            index.append(i)
        srl = doc["srl"]
        for ss in srl:
            
            for si in ss:
                tok, role, begin, end = si[0], si[1], si[2], si[3]
                begin_index, end_index = index[begin], index[end]
                lab = label[begin_index:end_index]
                # 同一个token，修复步骤：1、统计出现最多的标签，如果它不是交易方式，就将它标记为这个词的正确标签。
                # if end_index - begin_index == 1 and text[begin_index] != "不":
                #     label[begin_index] = "O"
                #     continue
                kvs = {}
                for l in lab:
                    if l != "O":
                        l = l[2:]
                    if l not in kvs:
                        kvs[l] = 1
                    else:
                        kvs[l] += 1
                a, b = "", 0
                for k in list(kvs.keys()):
                    if kvs[k] > b:
                        a = k
                        b = kvs[k]
                if b <= len(lab)*4/5:  # 限定改变，防止改变太多丢失信息
                    continue
                if a == "O":
                    for i in range(begin_index, end_index):
                        if "交易方式" not in label[i] and "交易品种" not in label[i]:
                            label[i] = "O"
                elif a != "交易方式" and a != "交易品种":
                    for i in range(begin_index, end_index):
                        if "交易方式" in label[i] and "交易品种" in label[i]:
                            continue
                        if i == begin_index:
                            label[i] = "B-" + a
                        else:
                            label[i] = "I-" + a
        
        # 特殊处理：时间、数量、价格以及key、value
        # 时间，一般形式为 时间 为 key，也可能出现key 为 时间
        iters = re.finditer(r"\d{1,2}:\d{1,2}", text)
        i = 0
        t_begin = 0
        for x in iters:
            a, b = x.start(), x.end()
            if t_begin == 0:
                t_begin = a
            if b < len(text) and text[b] != "至" and text[b] != "、":
                if t_begin > 6 and "每个交易日" in text[t_begin-6:t_begin]:
                    t_begin = t_begin - 6
                label = change(t_begin, b, label, "时间")
                t_begin = 0
        p = text.find("时间")
        while p != -1:
            a, b = p, p+2
            while a > 0 and text[a] not in punctuation:
                a-=1
            a+=1
            if text[b] in ["内"] and text[b+1] in punctuation:
                label = change(a, b+1, label, "时间")
            p = text.find("时间", b+1)
        # 数量，主要处理 ...或者其整数倍、不足...部分、直接 3种情况
        stopsignal = ["，", "。", "；", "的"]
        if "数量" in text:
            i = 0
            a, b = -1, -1
            while i < len(text):
                if text[i].isdigit():
                    a = i
                    while i < len(text) and text[i] not in stopsignal:
                        i += 1
                    b = i
                    c=a-1
                    while c >= 0 and text[c] not in stopsignal:
                        c-=1
                    if ("数量" in text[c:a] or "余额" in text[c:a]) and ":" not in text[a:b]:
                        if "整数倍" in text[a:b]:
                            b = text[a:b].find("整数倍") + a + 3
                            label = change(a, b, label, "数量")
                        elif a-2 > 0 and "不足" == text[a-2:a] and "部分" in text[a:b]:
                            a = a-2
                            if a-2>0 and text[a-2:a] == "余额":
                                a = a-2
                            b = text[a:b].find("部分") + a + 2
                            label = change(a, b, label, "数量")
                        else:
                            label = change(a, b, label, "数量")
                else:
                    i += 1
        # 价格
        if "价格" in text or "金额" in text:
            i = 0
            a, b = -1, -1
            while i < len(text):
                if text[i].isdigit():
                    a = i
                    while i < len(text) and text[i] not in stopsignal:
                        i += 1
                    b = i
                    c=a-1
                    while c >= 0 and text[c] not in stopsignal:
                        c-=1
                    if "价格" in text[c:a] or "金额" in text[c:a]:
                        if ":" not in text[a:b]:
                            label = change(a, b, label, "价格")
                else:
                    i += 1
        # key value
        i=0
        while i < len(text):
            # 寻找时间、数量、价格等
            if "时间" in label[i] or "数量" in label[i] or "价格" in label[i]:
                a = i
                i += 1
                while i < len(text) and label[i][2:] == label[i-1][2:]:
                    i += 1
                b = i
                if b - a < 3:  # 时间、数量、价格最少得3个字
                    continue
                if i < len(text) and text[i] == "为":
                    # 后面是key
                    i += 1
                    a_key = i
                    while i < len(text) and text[i] not in stopsignal:
                        i += 1
                    b_key = i
                    label = change(a_key, b_key, label, "key")
                    if "数量" in text[a_key:b_key]:
                        if "数量" not in label[a]:
                            label = change(a, b, label, "数量")
                    elif "价格" in text[a_key:b_key]:
                        if "价格" not in label[a]:
                            label = change(a, b, label, "价格")
                else:
                    # 前面是key
                    j = a
                    while j > 0 and text[j] not in stopsignal:
                        j -= 1
                    j += 1
                    while j < a and "O" != label[j] and "key" not in label[j]:
                        j += 1
                    a_key = j
                    while j < a and text[j] != "为":
                        j += 1
                    if j == a:
                        continue
                    b_key = j
                    if b_key-2 > a and "应当" == text[b_key-2:b_key]:
                        b_key -= 2
                    label = change(a_key, b_key, label, "key")
            else:
                i += 1
        

        # 2、部分标点符号标为O
        if not ("除" in text and "不接受" in text and "撤销" in text and "外" in text and "其他" in text and "申报" in text and "时间" in text):
            
            for i, t in enumerate(text):
                if t in punctuation:
                    label[i] = "O"

        # 3、“应当”设为O
        i = 0
        i = text.find("应")
        while i != -1:
            if i+1 < len(text) and (text[i+1] == "当" or text[i+1] == "该"):
                label[i] = label[i+1] = "O"
            else:
                label[i] = "O"
            i = text.find("应", i+1)
        # 4、有些申报方式不应该标为“交易方式”
        i = 0
        i = text.find("申报")
        while i != -1:
            if i-2>=0 and "交易方式" in label[i] and "交易方式" in label[i+1]:
                label = change(i-2, i+2, label, "value")
            i = text.find("申报", i+1)
        
        
        # 5、解决数量/价格 op/为 数量/价格的现象，将第一个数量/价格改为key
        i = 0
        count, l = 0, ""
        a, b = 0, 0
        while i < len(label):
            if "价格" in label[i]:
                if count == 0:
                    count = 1
                    l = "价格"
                    a = i
                elif count == 2:
                    if l == "价格":
                        # 将前面的价格改为key
                        label = change(a, b, label, "key")
                        while "价格" in label[i]:
                            i += 1
                        i-=1  # 结尾有一个统一的i+=1
                    else:  # 价格 op 数量
                        if is_price_key(text[a:b]):
                            label = change(a, b, label, "key")
                            a = i
                            while "数量" in label[i] or "价格" in label[i]:
                                i += 1
                            b = i
                            i-=1
                            label = change(a, b, label, "价格")
                        elif is_num_key(text[a:b]):
                            label = change(a, b, label, "key")
                            a = i
                            while "数量" in label[i] or "价格" in label[i]:
                                i += 1
                            b = i
                            i-=1
                            label = change(a, b, label, "数量")
                    count = 0
                    a = 0
                    b = 0
            elif "数量" in label[i]:
                if count == 0:
                    count = 1
                    l = "数量"
                    a = i
                elif count == 2:
                    if l == "数量":
                        label = change(a, b, label, "key")
                        while "数量" in label[i]:
                            i += 1
                        i-=1
                    else:
                        if is_price_key(text[a:b]):
                            label = change(a, b, label, "key")
                            a = i
                            while "数量" in label[i] or "价格" in label[i]:
                                i += 1
                            b = i
                            i-=1
                            label = change(a, b, label, "价格")
                        elif is_num_key(text[a:b]):
                            label = change(a, b, label, "key")
                            a = i
                            while "数量" in label[i] or "价格" in label[i]:
                                i += 1
                            b = i
                            i-=1
                            label = change(a, b, label, "数量")
                    count = 0
                    a = 0
                    b = 0
            elif "数量" not in label[i] and "价格" not in label[i]:
                if count == 1 and b == 0:
                    b = i
                if label[i] == "O" and text[i] == "为" or "op" in label[i]:
                    if count == 1:
                        count = 2
                else:
                    count = 0
            i += 1
        # 6、“上下”改为和前后一致的标签
        i=0
        i=text.find("上下")
        while i != -1:
            a, b = i-1, i+2
            a -= 1
            b += 1
            while a > 0:
                if label[a] != "O" and label[a] == label[a+1]:
                    a-=1
                else:
                    a += 1
                    label_a = label[a] if "-" not in label[a] else label[a][2:]
                    break
            while b < len(text):
                if label[b] != "O" and label[b] == label[b-1]:
                    b += 1
                else:
                    b -= 1
                    label_b = label[b] if "-" not in label[b] else label[b][2:]
                    break
            if label_a == label_b:
                label = change(a,b+1,label,label_a)
            else:
                label = change(a,b+1,label,label_b)
            i = text.find("上下", i+1)

        # 3、结束之后扫描一遍，如果改标签了，则将开始标签设为B-，中间设为I-
        last = "O"
        for i, l in enumerate(label):
            if i > 0 and "B-" in label[i-1]:
                if (l == "O" or l[2:] != last) and "or" not in label[i-1]:
                    label[i-1] = "O"
                    last = "O"
            if l != "O":
                l = l[2:]
                if l != last:
                    label[i] = "B-" + l
                else:
                    label[i] = "I-" + l
            last = l
        
        



        rule["text"], rule["label"] = text, " ".join(label)
    return tco

def token_classification(tci: list, knowledge, model_path: str, dict_file: str, batch_size: int = 8, sentence_max_length: int = 512):
    
    with open(dict_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
        num_labels = len(lines)

    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=num_labels)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs = []
        for item in items:
            inputs.append(item["text"].replace(" ", "")[:510])
        return inputs

    inputs = preprocess(tci)
    model.eval()
    device = try_gpu()
    model = model.to(device)

    def predict(inputs):
        
        hats = []
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            input_copy = batch.copy()
            batch = tokenizer(batch, max_length=sentence_max_length, padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.to(device)
            logits = model(input_ids=input_ids).logits
            _, outputs = torch.max(logits, dim=2)
            outputs = outputs.cpu().numpy()
            for i, output in enumerate(outputs):
                h = []
                for j in range(min(len(input_copy[i])+2, sentence_max_length)):
                    h.append(output[j])
                hats.append(h[1:-1])
        return hats
    
    with torch.no_grad():
        hats = predict(inputs)

    index_to_class, _ = read_dict(dict_file)
    class_hats = []
    for hat in hats:
        class_hat = []
        for h in hat:
            class_hat.append(index_to_class[h])
        class_hats.append(class_hat)
    
    tco = tci.copy()
    for i, rule in enumerate(tco):
        rule["label"] = " ".join(class_hats[i])
        rule['text'] = inputs[i]
    
    # 使用算法修复
    tco = token_classification_with_algorithm(tco, knowledge)
    
    return tco



if __name__ == "__main__":
    tci_data = json.load(open("rules_cache/tci.json", "r", encoding="utf-8"))
    knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    tco_data = token_classification(tci_data, knowledge, "../model/ours/best_1690329462", "../data/tc_data.dict")
    json.dump(tco_data, open("rules_cache/tco.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
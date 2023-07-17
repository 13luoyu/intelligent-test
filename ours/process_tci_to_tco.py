# token classification任务

import json
from token_classification import eval_model
from utils.arguments import arg_parser
from transformers import AutoModelForTokenClassification, AutoTokenizer
import torch
from utils.data_loader import read_dict
import hanlp

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

def token_classification_with_algorithm(tco, knowledge):
    # 所有可以补的标签：
    # 交易品种、交易方式、结合规则、结果、系统、or、时间、价格、数量、op
    # 还需要将标签修复完整
    for rule in tco:
        text, label = rule["text"], rule["label"].split(" ")
        # 交易品种
        types = []
        for key in knowledge:
            if "品种" in key and isinstance(knowledge[key], list):
                types += knowledge[key]
        for t in types:
            p = text.find(t)
            while p != -1:
                label = change(p, p+len(t), label, "交易品种")
                p = text.find(t, p+len(t))
        # 交易方式
        types = []
        for key in knowledge:
            if "交易方式" in key and isinstance(knowledge[key], list):
                types += knowledge[key]
        for t in types:
            p = text.find(t)
            while p != -1:
                label = change(p, p+len(t), label, "交易方式")
                p = text.find(t, p+len(t))
        # 结合规则
        # 第..条，本规则第..条，《》，《》第..条
        p1 = text.find("《")
        p2 = text.find("》")
        p3 = text.find("第", p2+1)
        p4 = text.find("条", p2+1)

        while p1 != -1:
            if p3>0 and p4>0 and p3-p2<=2:
                p4 = p4 + p2 + 1
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
                p4 = p4 + p2 + 1
                label = change(p1, p4+1, label, "结合规则")
            p1 = text.find("本规则", p1+3)
            p3 = text.find("第", p1+3)
            p4 = text.find("条", p1+3)

        p1 = text.find("第")
        p2 = text.find("条")
        while p1 != -1:
            if "结合规则" in label[p1] and "结合规则" in label[p2]:
                break
            label = change(p1, p2+1, label, "结合规则")
            p1 = text.find("第", p2+1)
            p2 = text.find("条", p2+1)

        # 结果
        p = text.find("可以")
        while p != -1:
            label = change(p, p+2, label, "结果")
            p = text.find(t, p+2)
        p = text.find("不得")
        while p != -1:
            label = change(p, p+2, label, "结果")
            p = text.find(t, p+2)
        p = text.find("不接受")
        while p != -1:
            label = change(p, p+3, label, "结果")
            p = text.find(t, p+3)
        p = text.find("有效")
        while p != -1:
            label = change(p, p+2, label, "结果")
            p = text.find(t, p+2)
        # 系统
        p = text.find("本所")
        while p != -1:
            label = change(p, p+2, label, "系统")
            p = text.find(t, p+2)
        # or
        p = text.find("或")
        while p != -1:
            label = change(p, p+1, label, "or")
            p = text.find(t, p+1)
        p = text.find("或者")
        while p != -1:
            label = change(p, p+2, label, "or")
            p = text.find(t, p+2)
        # op
        types = []
        for key in knowledge:
            if "本数" in key and isinstance(knowledge[key], list):
                types += knowledge[key]
        for t in types:
            p = text.find(t)
            while p != -1:
                label = change(p, p+len(t), label, "op")
                p = text.find(t, p+len(t))



        # 小修正，先分词，然后理论上同一组词应该具有相同的标签，如果连续不同的词具有相同的标签，应该是一个词
        HanLP = hanlp.load(hanlp.pretrained.mtl.CLOSE_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_BASE_ZH)
        doc = HanLP(text, tasks='srl')
        print(doc["srl"])




        rule["text"], rule["label"] = text, " ".join(label)
    return tco

def token_classification(in_file: str, out_file: str, knowledge_file: str, model_path: str, dict_file: str, batch_size: int = 8, sentence_max_length: int = 512):
    tci = json.load(open(in_file, "r", encoding="utf-8"))
    knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
    
    with open(dict_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
        num_labels = len(lines)

    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=num_labels)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs = []
        for item in items:
            inputs.append(item["text"].replace(" ", ""))
        return inputs

    inputs = preprocess(tci)

    def predict(model, tokenizer, inputs):
        model.eval()
        model = model.cuda()
        hats = []
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            input_copy = batch.copy()
            batch = tokenizer(batch, max_length=sentence_max_length, padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.cuda()
            logits = model(input_ids=input_ids).logits
            _, outputs = torch.max(logits, dim=2)
            outputs = outputs.cpu().numpy()
            for i, output in enumerate(outputs):
                h = []
                for j in range(min(len(input_copy[i])+2, sentence_max_length)):
                    h.append(output[j])
                hats.append(h[1:-1])
        return hats
    
    hats = predict(model, tokenizer, inputs)

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
    
    # 使用算法修复
    tco = token_classification_with_algorithm(tco, knowledge)
    
    json.dump(tco, open(out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)



if __name__ == "__main__":
    token_classification("rules_cache/tci.json", "rules_cache/tco.json", "../data/knowledge.json", "../model/ours/best_1689080207", "../data/tc_data.dict")
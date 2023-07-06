# token classification任务

import json
from token_classification import eval_model
from utils.arguments import arg_parser
from transformers import AutoModelForTokenClassification, AutoTokenizer
import torch
from utils.data_loader import read_dict

def token_classification_with_algorithm(tco, knowledge):
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
                for j in range(min(len(input_copy[i])+2), sentence_max_length):
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
    token_classification("rules_cache/tci.json", "rules_cache/tco.json", "../data/knowledge.json", "../model/ours/...", "../data/tc_data.dict")
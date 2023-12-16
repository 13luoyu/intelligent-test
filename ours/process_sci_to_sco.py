# sequence classification任务
import json
from transformers import AutoModelForSequenceClassification, AutoTokenizer
import torch
from utils.try_gpu import try_gpu


def sequence_classification_with_algorithm(sco):
    for sc in sco:
        if "可以在本所上市交易" in sc["text"] or "可以采用" in sc["text"] and "等方式" in sc["text"] or "即时行情" in sc["text"] or "，即" in sc["text"] or "本所交易系统处理" in sc["text"]:
            sc['type'] = "0"
    return sco


# def sequence_classification(in_file: str, out_file: str, model_path: str, batch_size: int = 8, sentence_max_length: int = 512):
def sequence_classification(sci: list, model_path: str, batch_size: int = 8, sentence_max_length: int = 512):
    model = AutoModelForSequenceClassification.from_pretrained(model_path, num_labels=3)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs = []
        for item in items:
            inputs.append(item["text"])
        return inputs
    
    inputs = preprocess(sci)
    model.eval()
    device = torch.device('cpu')
    model = model.to(device)

    def predict(inputs):
        hats = []
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            batch = tokenizer(batch, max_length=sentence_max_length, padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.to(device)
            logits = model(input_ids=input_ids).logits
            _, outputs = torch.max(logits, dim=1)
            outputs = outputs.cpu().numpy()
            hats.extend(outputs)
        return hats
    with torch.no_grad():
        hats = predict(inputs)
    sco = sci.copy()
    for i, rule in enumerate(sco):
        rule["type"] = str(hats[i])
    
    sco = sequence_classification_with_algorithm(sco)
    
    return sco



if __name__ == "__main__":
    sci_data = json.load(open("rules_cache/sci.json", "r", encoding="utf-8"))
    sco_data = sequence_classification(sci_data, "../model/ours/best_1690658708")
    json.dump(sco_data, open("rules_cache/sco.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

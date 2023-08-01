# sequence classification任务
import json
from transformers import AutoModelForSequenceClassification, AutoTokenizer
import torch


def sequence_classification(in_file: str, out_file: str, model_path: str, batch_size: int = 8, sentence_max_length: int = 512):
    sci = json.load(open(in_file, "r", encoding="utf-8"))
    model = AutoModelForSequenceClassification.from_pretrained(model_path, num_labels=3)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs = []
        for item in items:
            inputs.append(item["text"])
        return inputs
    
    inputs = preprocess(sci)
    
    def predict(model, tokenizer, inputs):
        model.eval()
        model = model.cuda()
        hats = []
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            batch = tokenizer(batch, max_length=sentence_max_length, padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.cuda()
            logits = model(input_ids=input_ids).logits
            _, outputs = torch.max(logits, dim=1)
            outputs = outputs.cpu().numpy()
            hats.extend(outputs)
        return hats
    
    hats = predict(model, tokenizer, inputs)
    sco = sci.copy()
    for i, rule in enumerate(sco):
        rule["type"] = str(hats[i])
    json.dump(sco, open(out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)




if __name__ == "__main__":
    sequence_classification("rules_cache/sci.json", "rules_cache/sco.json", "../model/ours/?")
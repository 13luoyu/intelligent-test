import torch
from transformers import AutoModelForTokenClassification, AutoTokenizer, AutoModel


model_path = "../model/mengzi-bert-base-fin"
model = AutoModel.from_pretrained(model_path, num_labels=35)
tokenizer = AutoTokenizer.from_pretrained(model_path)

model = model.eval()
print(model)
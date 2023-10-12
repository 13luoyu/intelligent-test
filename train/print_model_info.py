from transformers import AutoModel, AutoTokenizer, AutoModelForTokenClassification

def print_model_info(model_path):
    model = AutoModel.from_pretrained(model_path, num_labels=35)
    tokenizer = AutoTokenizer.from_pretrained(model_path)
    model = model.eval()
    print(model)
    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=37)
    print(model)


# model_path = "../model/mengzi-bert-base-fin"
model_path = "model"
print_model_info(model_path)
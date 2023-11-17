from transformers import AutoModelForSequenceClassification, AutoTokenizer, Trainer
from utils.data_loader import DefaultDataset, DataCollatorForSequenceClassification, read_json_for_sequence_classification, read_dict
from utils.training_arguments import get_training_arguments
from utils.arguments import arg_parser
import torch
import time
from utils.try_gpu import try_gpu


def train_model(train_dataset: str, eval_dataset: str, model_path: str, training_args = {}):

    model = AutoModelForSequenceClassification.from_pretrained(model_path, num_labels=3)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    train_dataset = DefaultDataset(read_json_for_sequence_classification(train_dataset, istrain=True))
    eval_dataset = DefaultDataset(read_json_for_sequence_classification(eval_dataset))
    collator = DataCollatorForSequenceClassification(tokenizer)

    saved_path = training_args["output_dir"]
    training_args = get_training_arguments(training_args)
    trainer = Trainer(model, training_args, collator, train_dataset, eval_dataset, tokenizer)
    trainer.train()

    saved_path = f"{saved_path}/best_{int(time.time())}"
    trainer.save_model(saved_path)
    return saved_path


def eval_model(eval_dataset: str, model_path: str, training_args = {}):

    model = AutoModelForSequenceClassification.from_pretrained(model_path, num_labels=3)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs, labels = [], []
        for item in items:
            inputs.append(item["text"])
            labels.append(int(item["label"]))
        return inputs, labels

    eval_dataset = read_json_for_sequence_classification(eval_dataset)
    inputs, labels = preprocess(eval_dataset)

    def predict(model, tokenizer, inputs, batch_size=8):
        model.eval()
        device = try_gpu()
        model = model.to(device)
        hats = []  # batch_size, 1
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            batch = tokenizer(batch, max_length=512, padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.to(device)
            logits = model(input_ids=input_ids).logits  # (8, 2)
            _, outputs = torch.max(logits, dim=1)
            outputs = outputs.cpu().numpy()  # (8)
            hats.extend(outputs)
        return hats

    hats = predict(model, tokenizer, inputs)
    
    with open(f"../log/sc_eval_{model_path.split('_')[-1]}.log", "w+", encoding="utf-8") as f:
        f.write("预测结果：\n")
        correct = 0
        for i, data in enumerate(eval_dataset):
            f.write(f"id: {i}\ntext: {inputs[i]}\nseq hat: {hats[i]}\nseq real: {labels[i]}\n")
            f.write("----------------------------------------------------\n\n")
            if(hats[i] == labels[i]):
                correct += 1
        f.write(f"统计结果：\n测试集数据数量：{len(eval_dataset)}，预测正确数量：{correct}，正确率：{float(correct) / float(len(eval_dataset))}")
        f.write("\n\n\n\n\n\n\n\n\n\n")



if __name__ == "__main__":
    training_args = arg_parser()
    model = training_args["model"]
    saved_path = train_model(training_args["train_dataset"], training_args["validate_dataset"], model, training_args)
    eval_model(training_args["validate_dataset"], saved_path, training_args)
    # saved_path = "../model/ours/best_1690658708"
    # eval_model("../data/sc_validate_data.json", saved_path, training_args)
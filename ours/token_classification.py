from transformers import AutoModelForTokenClassification, AutoTokenizer, Trainer
from utils.data_loader import DefaultDataset, DataCollatorForTokenClassification, read_json_for_token_classification, read_dict
from utils.training_arguments import get_training_arguments
from utils.arguments import arg_parser
import torch
import time
from utils.try_gpu import try_gpu


def printlog(s):
    with open("run.log", "a+") as f:
        f.write(str(s))
        f.write("\n")


class CustomTrainer(Trainer):
    def compute_loss(self, model, inputs, return_outputs=False):
        # inputs.input_ids, inputs.labels: (batch_size, sentence_length)
        # inputs.logits: (batch_size, sentence_length, label_num)
        labels = inputs.get("labels")
        # forward pass
        outputs = model(**inputs)
        logits = outputs.get("logits")
        # compute custom loss (suppose one has 3 labels with different weights)
        # loss_fct = torch.nn.CrossEntropyLoss(weight=torch.tensor([1.0, 2.0, 3.0], device=model.device))
        loss_fct = torch.nn.CrossEntropyLoss()
        loss = loss_fct(logits.view(-1, self.model.config.num_labels), labels.view(-1))
        return (loss, outputs) if return_outputs else loss


def train_model(train_dataset: str, eval_dataset: str, class_dict: str, model_path: str, training_args = {}):

    with open(class_dict, "r", encoding="utf-8") as f:
        lines = f.readlines()
        num_labels = len(lines)

    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=num_labels)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    train_dataset = DefaultDataset(read_json_for_token_classification(train_dataset, istrain=True))
    eval_dataset = DefaultDataset(read_json_for_token_classification(eval_dataset))
    collator = DataCollatorForTokenClassification(tokenizer, class_dict, max_length=training_args["sentence_max_length"], split = training_args["split"])

    saved_path = training_args["output_dir"]
    training_args = get_training_arguments(training_args)
    trainer = Trainer(model, training_args, collator, train_dataset, eval_dataset, tokenizer)
    trainer.train()

    saved_path = f"{saved_path}/best_{int(time.time())}"
    trainer.save_model(saved_path)
    return saved_path


def eval_model(eval_dataset: str, class_dict: str, model_path: str, training_args = {}):

    with open(class_dict, "r", encoding="utf-8") as f:
        lines = f.readlines()
        num_labels = len(lines)

    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=num_labels)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs, labels = [], []
        for item in items:
            inputs.append(item["text"].replace(training_args["split"], ""))
            labels.append(item["label"].replace(training_args["split"], " "))
        return inputs, labels

    eval_dataset = read_json_for_token_classification(eval_dataset)
    inputs, labels = preprocess(eval_dataset)

    def predict(model, tokenizer, inputs, batch_size=8):
        model.eval()
        device = try_gpu()
        model = model.to(device)
        hats = []  # batch_size, sentence_length
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            input_copy = batch
            batch = tokenizer(batch, max_length=training_args["sentence_max_length"], padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.to(device)
            attention_mask = batch.attention_mask
            logits = model(input_ids=input_ids).logits  # (8, training_args["sentence_max_length"], num_labels)
            _, outputs = torch.max(logits, dim=2)
            outputs = outputs.cpu().numpy()
            for i, output in enumerate(outputs):  # (8, training_args["sentence_max_length"])
                # mask = attention_mask[i]
                h = []
                for j in range(min(len(input_copy[i]) + 2, training_args["sentence_max_length"])):
                    h.append(output[j])
                hats.append(h[1:-1])  # h[0]是<cls>
        return hats

    hats = predict(model, tokenizer, inputs)

    index_to_class, _ = read_dict(class_dict)
    class_hats = []
    for hat in hats:
        class_hat = []
        for h in hat:
            class_hat.append(index_to_class[h])
        class_hats.append(class_hat)
    
    with open(f"../log/tc_eval_{model_path.split('_')[-1]}.log", "w+", encoding="utf-8") as f:
        f.write("预测结果：\n")
        for i, data in enumerate(eval_dataset):
            f.write(f"id: {i}\ntext: {inputs[i]}\nir hat: {' '.join(class_hats[i])}\nir real: {labels[i]}\n")
            f.write("----------------------------------------------------\n\n")
        f.write("\n\n\n\n\n\n\n\n\n\n")



if __name__ == "__main__":
    training_args = arg_parser()
    model = training_args["model"]
    # saved_path = train_model(training_args["train_dataset"], training_args["validate_dataset"], "../data/tc_data.dict", model, training_args)
    saved_path = "../model/ours/best_1696264421"
    eval_model(training_args["validate_dataset"], "../data/tc_data.dict", saved_path, training_args)
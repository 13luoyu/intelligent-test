from transformers import AutoModelForTokenClassification, AutoTokenizer, Trainer, TrainingArguments
from encoder_fine_tuning.data_loader import DefaultDataset, DataCollatorForTokenClassification, read_json_for_token_classification, read_dict
from encoder_fine_tuning.arguments import arg_parser
import torch
import time
import os


def get_training_arguments(training_args):
    num_train_epochs = training_args["num_train_epochs"]
    per_device_train_batch_size = training_args["per_device_train_batch_size"]
    per_device_eval_batch_size = training_args["per_device_eval_batch_size"]
    logging_step = training_args["logging_step"]
    evaluation_strategy = training_args["evaluation_strategy"]
    eval_steps = training_args["eval_steps"]
    load_best_model_at_end = training_args["load_best_model_at_end"]
    learning_rate = training_args["learning_rate"]
    output_dir = training_args["output_dir"]
    save_total_limit = training_args["save_total_limit"]
    lr_scheduler_type = training_args["lr_scheduler_type"]
    gradient_accumulation_steps = training_args["gradient_accumulation_steps"]
    dataloader_num_workers = training_args["dataloader_num_workers"]
    remove_unused_columns = training_args["remove_unused_columns"]
    logging_dir = training_args["logging_dir"]
    save_strategy = training_args["save_strategy"]
    save_steps = training_args["save_steps"]
    disable_tqdm = training_args["disable_tqdm"]
    weight_decay = training_args["weight_decay"]

    training_args = TrainingArguments(
        num_train_epochs=num_train_epochs,
        per_device_train_batch_size=per_device_train_batch_size,
        per_device_eval_batch_size=per_device_eval_batch_size,
        logging_steps=logging_step,
        evaluation_strategy=evaluation_strategy,
        eval_steps=eval_steps,
        load_best_model_at_end=load_best_model_at_end,
        learning_rate=learning_rate,
        output_dir=output_dir,
        save_total_limit=save_total_limit,
        lr_scheduler_type=lr_scheduler_type,
        gradient_accumulation_steps=gradient_accumulation_steps,
        dataloader_num_workers=dataloader_num_workers,
        remove_unused_columns=remove_unused_columns,
        logging_dir=logging_dir,
        save_strategy=save_strategy,
        save_steps=save_steps,
        disable_tqdm=disable_tqdm,
        weight_decay=weight_decay
    )
    return training_args



def try_gpu(i=0):
    if torch.cuda.device_count() >= i + 1:
        return torch.device(f'cuda:{i}')
    return torch.device('cpu')

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
    args = get_training_arguments(training_args)
    trainer = Trainer(model, args, collator, train_dataset, eval_dataset, tokenizer)
    trainer.train()

    base_model = ""
    if "mengzi" in training_args['model']:
        base_model = "mengzi"
    elif "finbert" in training_args['model']:
        base_model = "finbert"
    saved_path = f"{saved_path}/{base_model}_tc_{int(time.time())}"
    trainer.save_model(saved_path)
    return saved_path


def eval_model(eval_dataset: str, class_dict: str, model_path: str, output_filename: str, training_args: dict):

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
    
    with open(output_filename, "w+", encoding="utf-8") as f:
        f.write("预测结果：\n")
        for i, data in enumerate(eval_dataset):
            f.write(f"id: {i}\ntext: {inputs[i]}\nir hat: {' '.join(class_hats[i])}\nir real: {labels[i]}\n")
            f.write("----------------------------------------------------\n\n")
        f.write("\n\n\n\n\n\n\n\n\n\n")



if __name__ == "__main__":
    training_args = arg_parser()
    model = training_args["model"]
    saved_path = train_model(training_args["train_dataset"], training_args["validate_dataset"], "../data/data_for_LLM_encoder/tc_data.dict", model, training_args)
    # saved_path = "../model/trained/mengzi_rule_element_extraction"
    eval_model(training_args["validate_dataset"], "../data/data_for_LLM_encoder/tc_data.dict", saved_path, "./predict_data/"+saved_path.split("/")[-1]+"_test_result.txt", training_args)
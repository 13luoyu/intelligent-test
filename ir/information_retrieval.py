from transformers import AutoModelForTokenClassification, AutoTokenizer, Trainer
from utils.data_loader import DefaultDataset, DataCollatorForTokenClassification, read_tsv, read_dict
from utils.training_arguments import get_training_arguments
from utils.arguments import arg_parser
import torch
import time

# run command: nohup python information_retrieval.py --output_dir ../model/ir --disable_tqdm True >../log/run_ir.log &


def train_ir_model(train_dataset: str, eval_dataset: str, class_dict: str, model_path: str, training_args = {}):

    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=121)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    train_dataset = DefaultDataset(read_tsv(train_dataset, istrain=True))
    eval_dataset = DefaultDataset(read_tsv(eval_dataset))
    collator = DataCollatorForTokenClassification(tokenizer, class_dict, training_args["split"])

    saved_path = training_args["output_dir"]
    training_args = get_training_arguments(training_args)
    trainer = Trainer(model, training_args, collator, train_dataset, eval_dataset, tokenizer)
    trainer.train()

    saved_path = f"{saved_path}/best_{int(time.time())}"
    trainer.save_model(saved_path)
    return saved_path


def eval_ir_model(eval_dataset: str, class_dict: str, model_path: str, training_args = {}):

    model = AutoModelForTokenClassification.from_pretrained(model_path, num_labels=121)
    tokenizer = AutoTokenizer.from_pretrained(model_path)

    def preprocess(items):
        inputs, labels = [], []
        for item in items:
            inputs.append(item["text"].replace(training_args["split"], ""))
            labels.append(item["label"].replace(training_args["split"], ""))
        return inputs, labels

    eval_dataset = read_tsv(eval_dataset)
    inputs, labels = preprocess(eval_dataset)

    def predict(model, tokenizer, inputs, batch_size=8):
        model.eval()
        model = model.cuda()
        hats = []  # batch_size, sentence_length
        for start in range(0, len(inputs), batch_size):
            batch = inputs[start:start+batch_size]
            batch = tokenizer(batch, max_length=512, padding="max_length", truncation=True, return_tensors="pt")
            input_ids = batch.input_ids.cuda()
            attention_mask = batch.attention_mask
            logits = model(input_ids=input_ids).logits  # (8, 512, 121)
            _, outputs = torch.max(logits, dim=2)
            outputs = outputs.cpu().numpy()
            for i, output in enumerate(outputs):  # (8, 512)
                mask = attention_mask[i]
                h = []
                for j, d in enumerate(mask):
                    if d == 1:
                        h.append(output[j])
                    else:
                        h.append(output[j])  # 因为h[0]是<cls>，所以这里要加一个
                        break
                hats.append(h[1:])  # h[0]是<cls>
        
        return hats

    hats = predict(model, tokenizer, inputs)

    index_to_class, _ = read_dict(class_dict)
    class_hats = []
    for hat in hats:
        class_hat = []
        for h in hat:
            class_hat.append(index_to_class[h])
        class_hats.append(class_hat)
    
    with open(f"../log/eval_ir_{model_path.split('_')[-1]}.log", "a+", encoding="utf-8") as f:
        f.write("预测结果：\n")
        for i, data in enumerate(eval_dataset):
            f.write(f"id: {i}\ntext: {inputs[i]}\nir hat: {''.join(class_hats[i])}\nir real: {labels[i]}\n")
            f.write("----------------------------------------------------\n\n")
        f.write("\n\n\n\n\n\n\n\n\n\n")



if __name__ == "__main__":
    training_args = arg_parser()
    model = training_args["model"]
    saved_path = train_ir_model("../data/ir_train.tsv", "../data/ir_dev.tsv", "../data/ir.dict", model, training_args)
    eval_ir_model("../data/ir_dev.tsv", "../data/ir.dict", saved_path, training_args)
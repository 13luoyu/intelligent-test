from utils.data_loader import read_json
from transformers import BertTokenizer, EncoderDecoderModel, Seq2SeqTrainingArguments, Seq2SeqTrainer
from utils.arguments import arg_parser


def preprocess(items):
    inputs, labels = [], []
    for item in items:
        inputs.append(item["nl"])
        labels.append(item["R0"])
    return inputs, labels

def predict(model, tokenizer, sources, batch_size=8):
    model.eval()
    model = model.cuda()
    outputs = []
    for start in range(0, len(sources), batch_size):
        batch = sources[start:start+batch_size]
        inputs = tokenizer(batch, return_tensors="pt", truncation=True, padding="max_length", max_length=512)
        input_ids = inputs.input_ids.cuda()
        attention_mask = inputs.attention_mask.cuda()
        output = model.generate(input_ids=input_ids, attention_mask=attention_mask)
        outputs.extend(output)
    return tokenizer.batch_decode(outputs, skip_special_tokens=True)



def eval_model(eval_dataset, model_path, logging_dir="log/mengzi-bert-base-fin-aftertrained.log"):
    eval_data = read_json(eval_dataset)
    tokenizer = BertTokenizer.from_pretrained(model_path)
    model = EncoderDecoderModel.from_pretrained(model_path)
    inputs, refs = preprocess(eval_data)
    generations = predict(model, tokenizer, inputs)
    with open(logging_dir, "w+", encoding="utf-8") as f:
        f.write("预测结果：\n")
        for i, data in enumerate(eval_data):
            f.write(f"id: {data['id']}\nnatural language: {data['nl']}\nR0 hat: {generations[i]}\nR0 real: {data['R0']}\n")
            f.write("\n")
        f.write("----------------------------------------------------\n\n")





if __name__ == "__main__":
    training_args = arg_parser()
    eval_model("train_data.json", f"{training_args['after_trained_model_path']}/best", logging_dir="log/mengzi-bert-base-fin-aftertrained.log")
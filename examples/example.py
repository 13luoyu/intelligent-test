import json
from transformers import T5Tokenizer, T5ForConditionalGeneration, TrainingArguments, Trainer
from tqdm import tqdm  # 显示进度条
import random
from rouge import Rouge

def read_json(input_file):
    with open(input_file, 'r', encoding="utf-8") as f:
        lines = f.readlines()
    
    # tqmd()  用于显示进度条
    # map(function, iterable, ...)，对iterable的每个元素执行function
    datas = list(map(json.loads, tqdm(lines, desc="Reading...")))
    return datas


class Seq2SeqDataset:
    def __init__(self, data):
        self.datas = data

    def __len__(self):
        return len(self.datas)

    def __getitem__(self, index):
        return self.datas[index]

class DataCollatorForSeq2Seq:
    def __init__(self, tokenizer, padding: bool = True, max_length: int = 512):
        self.tokenizer = tokenizer
        #self.model = model
        self.padding = padding
        self.max_length = max_length

    def __call__(self, batch):
        features = self.collator_fn(batch)
        return features


    def preprocess(self, item):  # 获取数据
        source = item["abst"]
        target = item["title"]
        return source, target

    def collator_fn(self, batch):  # 处理函数，主要将json的list转化为tensor的inputs和labels
        results = map(self.preprocess, batch)
        inputs, targets = zip(*results)

        input_tensor = self.tokenizer(inputs,
                                      truncation=True,  # 截断
                                      padding=True,  # 填充
                                      max_length=self.max_length,
                                      return_tensors="pt",  # pytorch模型 或 "tf" tensorflow模型
                                      )

        target_tensor = self.tokenizer(targets,
                                       truncation=True,
                                       padding=True,
                                       max_length=self.max_length,
                                       return_tensors="pt",
                                       )

        input_tensor["labels"] = target_tensor["input_ids"]

        if "token_type_ids" in input_tensor:
            del input_tensor["token_type_ids"]
        return input_tensor


def preprocess(items):
    inputs, titles = [], []
    for item in items:
        inputs.append(item["abst"])
        titles.append(item["title"])
    return inputs, titles

def predict(model, tokenizer, sources, batch_size=8):
    model.eval()
    kwargs = {"num_beams":4}
    outputs = []
    for start in tqdm(range(0, len(sources), batch_size)):
        batch = sources[start:start+batch_size]
        input_tensor = tokenizer(batch, return_tensors="pt", truncation=True, padding=True, max_length=512).input_ids.cuda()
        outputs.extend(model.generate(input_ids=input_tensor, **kwargs))
    return tokenizer.batch_decode(outputs, skip_special_tokens=True)


def rouge_score(rouge, candidate, reference):
    text1 = " ".join(list(candidate))
    text2 = " ".join(list(reference))
    score = rouge.get_scores(text1, text2)
    return score

def compute_rouge(rouge, preds, refs):
    r1, r2, R_L = [], [], []
    for pred, ref in zip(preds, refs):
        scores = rouge_score(rouge, pred, ref)
        r1.append(scores[0]["rouge-1"]["f"])
        r2.append(scores[0]["rouge-2"]["f"])
        R_L.append(scores[0]["rouge-l"]["f"])
    return sum(r1)/len(r1), sum(r2)/len(r2), sum(R_L)/len(R_L)


if __name__ == "__main__":
    # 加载数据集
    trainset = read_json("csl_title_public/csl_title_train.json")
    test = read_json("csl_title_public/csl_title_dev.json")
    random.shuffle(trainset)
    train = trainset[:2500]
    dev = trainset[2500:]
    print("一个示例:", train[0])

    model_path = "mengzi-t5-base"
    Mengzi_tokenizer = T5Tokenizer.from_pretrained(model_path)
    Mengzi_model = T5ForConditionalGeneration.from_pretrained(model_path)

    trainset = Seq2SeqDataset(train)
    devset = Seq2SeqDataset(dev)
    collator = DataCollatorForSeq2Seq(Mengzi_tokenizer)

    # 训练模型
    training_args = TrainingArguments(
        num_train_epochs=3,  # epochs
        per_device_train_batch_size=8,  # batch size
        logging_steps=10,  # 每10步记录日志
        evaluation_strategy="steps",  # Evaluation is done (and logged) every eval_steps.也可以设为"epoch"
        eval_steps=100,  # 每100步进行一次evaluation
        load_best_model_at_end=True,
        learning_rate=1e-5,
        output_dir="test",  # 模型checkpoint的保存目录
        save_total_limit=5,  # If a value is passed, will limit the total amount of checkpoints. Deletes the older checkpoints in output_dir
        lr_scheduler_type='constant',  # lr不变
        gradient_accumulation_steps=1,  # Number of updates steps to accumulate the gradients for, before performing a backward/update pass.
        dataloader_num_workers=0,
        remove_unused_columns=False
    )

    trainer = Trainer(
        tokenizer=Mengzi_tokenizer,
        model=Mengzi_model,
        args=training_args,
        data_collator=collator,
        train_dataset=trainset,
        eval_dataset=devset
    )

    trainer.train()
    trainer.save_model("test/best")  # 保存最好的模型


    # 模型推理
    best_model = "test/best"
    tokenizer = T5Tokenizer.from_pretrained(best_model)
    model = T5ForConditionalGeneration.from_pretrained(best_model).cuda()
    inputs, refs = preprocess(test)
    generations = predict(model, tokenizer, inputs)
    print("原文: ", inputs[0])
    print("摘要: ", refs[0])
    print("预测: ", generations[0])

    # 生成结果的评测
    # 一个示例
    hypothesis = "the #### transcript is a written version of each day 's cnn student news program use this transcript to help students with reading comprehension and vocabulary use the weekly newsquiz to test your knowledge of storie s you saw on cnn student news"
    reference = "this page includes the show transcript use the transcript to help students with reading comprehension and vocabulary at the bottom of the page , comment for a chance to be mentioned on cnn student news . you must be a teacher or a student age # # or older to request a mention on the cnn student news roll call . the weekly newsquiz tests students ' knowledge of even ts in the news"
    rouge = Rouge()
    scores = rouge.get_scores(hypothesis, reference)

    # 评测
    rouge = Rouge()
    R_1, R_2, R_L = compute_rouge(rouge, generations, refs)
    print(R_1, R_2, R_L)
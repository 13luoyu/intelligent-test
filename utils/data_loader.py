import json
import torch
import random




# 数据集
class DefaultDataset:
    def __init__(self, data):
        self.datas = data

    def __len__(self):
        return len(self.datas)

    def __getitem__(self, index):
        return self.datas[index]

# seq2seq的数据加载器，将一个batch的自然语言编码为向量
class DataCollatorForSeq2Seq:
    def __init__(self, tokenizer, max_length: int = 512, padding = "max_length", truncation: bool = True):
        self.tokenizer = tokenizer
        self.padding = padding
        self.truncation = truncation
        self.max_length = max_length

    def __call__(self, batch):
        features = self.collator_fn(batch)
        return features


    def preprocess(self, item):  # 获取数据
        source = item["nl"]
        target = item["R0"]
        return source, target

    def collator_fn(self, batch):  # 处理函数，主要将json的list转化为tensor的inputs和labels
        results = map(self.preprocess, batch)
        inputs, targets = zip(*results)

        input_tensor = self.tokenizer(inputs,
                                      truncation=self.truncation,  # 截断
                                      padding=self.padding,  # 填充
                                      max_length=self.max_length,
                                      return_tensors="pt",  # pytorch模型 或 "tf" tensorflow模型
                                      )
        
        target_tensor = self.tokenizer(targets,
                                       truncation=self.truncation,
                                       padding=self.padding,
                                       max_length=self.max_length,
                                       return_tensors="pt",
                                       )


        input_tensor["decoder_input_ids"] = target_tensor["input_ids"]
        input_tensor["decoder_attention_mask"] = target_tensor["attention_mask"]
        input_tensor["labels"] = target_tensor["input_ids"].clone()
        # input_tensor["labels"] = torch.tensor([[-100 if token == self.tokenizer.pad_token_id else token for token in labels] for labels in input_tensor["labels"]])
        return input_tensor






# For Information Retrieval

def read_tsv(file: str, istrain: bool = False):
    with open(file, "r") as f:
        lines = f.readlines()
    id_data = []
    for i, line in enumerate(lines):
        if i == 0:
            continue
        x, y = line.strip().split("\t")
        id_data.append({"text":x, "label":y})
    if istrain:
        random.shuffle(id_data)
    return id_data

def read_json_for_token_classification(file: str, istrain: bool = False):
    id_data = []
    ds = json.load(open(file, "r", encoding="utf-8"))
    for d in ds:
        x, y = d["text"], d["label"]
        id_data.append({"text":x, "label":y})
    if istrain:
        random.shuffle(id_data)
    return id_data

class class_dict:
    def __init__(self):
        self.data = {}
    def __len__(self):
        return len(self.data.keys())
    def __setitem__(self, key, item):
        self.data[str(key)] = item
    def __getitem__(self, index):
        if str(index) in self.data:
            dt = self.data[str(index)]
        else:
            dt = "O"
        if dt.isdigit():
            return int(dt)
        return dt
    def __str__(self) -> str:
        return str(self.data)


def read_dict(file: str):
    with open(file) as f:
        lines = f.readlines()
    index_to_class = class_dict()
    class_to_index = class_dict()
    for line in lines:
        index, class_name = line.strip().split("\t")
        class_to_index[class_name] = index
        index_to_class[index] = class_name
    return index_to_class, class_to_index


# 分类任务数据加载器，将一个batch的自然语言编码为向量
class DataCollatorForTokenClassification:
    def __init__(self, tokenizer, class_dict: str, max_length: int = 512, padding = "max_length", truncation: bool = True, split: str = "\x02"):
        self.tokenizer = tokenizer
        self.padding = padding
        self.truncation = truncation
        self.max_length = max_length
        _, self.class_to_index = read_dict(class_dict)
        self.split = split


    def __call__(self, batch):
        features = self.collator_fn(batch)
        return features


    def preprocess(self, item):  # 获取数据
        if self.split == "\x02":
            source = item["text"].replace("\x02", "")
            target = item["label"].split("\x02")
        elif self.split == " ":
            source = item["text"]
            target = item["label"].split(" ")
        return source, target

    def collator_fn(self, batch):  # 处理函数，主要将json的list转化为tensor的inputs和labels
        results = map(self.preprocess, batch)
        inputs, targets = zip(*results)

        input_tensor = self.tokenizer(inputs,
                                      truncation=self.truncation,  # 截断
                                      padding=self.padding,  # 填充
                                      max_length=self.max_length,
                                      return_tensors="pt",  # pytorch模型 或 "tf" tensorflow模型
                                      )
        # 规则是这样的，在开头加上[CLS]，然后是正文，然后是[SEP]，最后是[PAD]
        # 如果正文过长，则为[CLS]+正文+[SEP]
        # 无论如何，都是max_length长度
        labels = []
        for target in targets:
            label = [self.class_to_index['O']]  # <cls>对应的是-100
            for y in target:
                label.append(self.class_to_index[y])
            if self.max_length - len(label) > 0:
                label += [self.class_to_index['O']] * (self.max_length - len(label))  # [PAD]和[SEP]对应O
            label = label[:self.max_length]
            label[-1] = self.class_to_index['O']  # 最后一个一定是[PAD]或[SEP]，对应-100
            labels.append(label)
        
        input_tensor["labels"] = torch.tensor(labels)

        return input_tensor












def read_json_for_sequence_classification(file: str, istrain: bool = False):
    id_data = []
    ds = json.load(open(file, "r", encoding="utf-8"))
    for d in ds:
        x, y = d["text"], d["type"]
        id_data.append({"text":x, "label":y})
    if istrain:
        random.shuffle(id_data)
    return id_data


class DataCollatorForSequenceClassification:
    def __init__(self, tokenizer, max_length: int = 512, padding = "max_length", truncation: bool = True):
        self.tokenizer = tokenizer
        self.padding = padding
        self.truncation = truncation
        self.max_length = max_length


    def __call__(self, batch):
        features = self.collator_fn(batch)
        return features


    def preprocess(self, item):  # 获取数据
        source = item["text"]
        target = item["label"]
        return source, target

    def collator_fn(self, batch):  # 处理函数，主要将json的list转化为tensor的inputs和labels
        results = map(self.preprocess, batch)
        inputs, targets = zip(*results)

        input_tensor = self.tokenizer(inputs,
                                      truncation=self.truncation,  # 截断
                                      padding=self.padding,  # 填充
                                      max_length=self.max_length,
                                      return_tensors="pt",  # pytorch模型 或 "tf" tensorflow模型
                                      )
        labels = [int(t) for t in targets]
        
        input_tensor["labels"] = torch.tensor(labels)

        return input_tensor
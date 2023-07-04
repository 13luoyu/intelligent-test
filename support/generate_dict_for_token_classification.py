# 读json格式的标注好的ir数据文件，生成所有标签类别的dict
import json


def generate_dict(data_file, data_dict):
    rules = json.load(open(data_file, "r", encoding="utf-8"))
    ds = []
    for rule in rules:
        label = rule["label"]
        tokens = label.split(" ")
        for token in tokens:
            if token not in ds:
                ds.append(token)
    with open(data_dict, "w+", encoding="utf-8") as f:
        for i, d in enumerate(ds):
            f.write(f"{i}\t{d}\n")




if __name__ == "__main__":
    generate_dict("../data/tc_train_data_all_base.json", "../data/tc_data.dict")
from nlpcda import Ner
import os
import json


def preprocess(input_file, output_dir):
    data = json.load(open(input_file, "r", encoding="utf-8"))
    for index, rule in enumerate(data):
        out_fp = open(output_dir + f"data{index}.txt", "w", encoding="utf-8")
        labels = rule["label"].split(" ")
        for i, text in enumerate(rule["text"]):
            label = labels[i]
            out_fp.write(f"{text}\t{label}\n")
        out_fp.close()


def data_augment(origin_file, input_dir, output_file):
    ner = Ner(ner_dir_name=input_dir,
            ignore_tag_list=['O'],
            # 不增强的标签有：结合规则、or、op、系统
            data_augument_tag_list=["key", "时间", "数量", "价格", "交易方式", "交易品种", "操作人", "操作", "操作部分", "结果", "状态","事件", "value"],
            augument_size=3, seed=0)
    
    rules = json.load(open(origin_file, "r", encoding="utf-8"))
    new_rules = []
    for i, file in enumerate(os.listdir(input_dir)):
        data_sentence_arrs, data_label_arrs = ner.augment(file_name=input_dir + file)
        # 3条增强后的句子、标签 数据，len(data_sentence_arrs)==3
        # 你可以写文件输出函数，用于写出，作为后续训练等
        # print(data_sentence_arrs, data_label_arrs)
        # exit(0)
        origin_id = rules[i]["id"]
        for j, text in enumerate(data_sentence_arrs):
            label = data_label_arrs[j]
            new_id = origin_id + f".argument{j}"
            rule = {
                "id": new_id,
                "text": "".join(text),
                "label": " ".join(label)
            }
            new_rules.append(rule)
    rules += new_rules
    json.dump(rules, open(output_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


if __name__ == "__main__":
    preprocess("../data/tc_train_data_base.json", "../data/unaugment_data_cache/")
    data_augment("../data/tc_train_data_base.json", "../data/unaugment_data_cache/", "../data/tc_train_data_full.json")
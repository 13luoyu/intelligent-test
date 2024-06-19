from transformers import AutoConfig, AutoTokenizer, AutoModelForCausalLM, HfArgumentParser
import torch
import json
from tqdm import tqdm
from dataclasses import dataclass, field
from typing import Optional


# python predict.py --model_name_or_path ./output/best_model_dev_dev_acc0_9898 --tokenizer_fast false --eval_dataset ../data/dev_ir.csv --prediction_file ./predict_data/predict_result_.json --mode base

@dataclass
class PredictionArguments:
    model_name_or_path: Optional[str] = field(default=None, metadata={"help":"模型存储的地址"})
    mode: Optional[str] = field(default=None, metadata={"help":"模型加载模式","choices":["base", "8bit-base"]})
    tokenizer_fast: Optional[bool] = field(default=None, metadata={"help":"是否使用快速tokenizer"})
    eval_dataset: Optional[str] = field(default=None, metadata={"help":"验证数据集地址"})
    prediction_file: Optional[str] = field(default=None, metadata={"help":"验证结果写入的文件"})



def get_trained_model_and_tokenizer(model_name_or_path, mode, tokenizer_fast):
    """
    加载模型
    model_name_or_path: model的路径
    load_in_8bit: 是否以8bit加载模型
    tokenizer_fast: 是否使用fast tokenizer
    output_name: 合并后模型保存的路径，如果为None则不保存
    """
    # 加载model
    # bfloat16 的表示范围比 float16 更广，但是精度更低
    if mode == "8bit-base":
        model = AutoModelForCausalLM.from_pretrained(model_name_or_path, return_dict=True, torch_dtype=torch.float16, device_map='auto', trust_remote_code=True, load_in_8bit = True, use_flash_attention_2=True)
    elif mode == "base":
        model = AutoModelForCausalLM.from_pretrained(model_name_or_path, return_dict=True, torch_dtype=torch.float16, device_map='auto', trust_remote_code=True, use_flash_attention_2=True)
    else:
        raise ValueError(f"未指定加载模型的模式 --mode, 必须为 \"base\", \"8bit-base\" 之一")
    # tokenizer
    tokenizer = AutoTokenizer.from_pretrained(model_name_or_path, use_fast=tokenizer_fast)
    # config
    config = AutoConfig.from_pretrained(model_name_or_path)
    architecture = config.architectures[0]
    print("模型结构", architecture)
    model.eval()
    
    return model, tokenizer


def get_datas(file_path):
    inputs, targets = [], []
    with open(file_path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    i, t = "", ""
    stage = 0
    for line in lines[1:]:
        line = line.replace("\"", "")
        if "<s>" in line:
            if "</s>" in line:
                i += line.split("Assistant:")[0] + "Assistant: "
                t += line.split("Assistant:")[1]
                stage += 1
            else:
                i += line
                stage += 1
        elif "</s>" in line:
            t += line.strip()
            inputs.append(i)
            targets.append(t)
            i, t = "", ""
            stage = 0
        elif stage == 1:
            i += line
    return inputs, targets

def generate_prediction(model, tokenizer, inputs, targets):
    predictions = []
    for index in tqdm(range(len(inputs))):
        print(f"### {index}")
        i = inputs[index]
        t = targets[index]
        input_ids = tokenizer([i], return_tensors="pt", add_special_tokens=False).input_ids
        if torch.cuda.is_available():
            input_ids = input_ids.to('cuda')
        generate_ids = model.generate(input_ids=input_ids, max_new_tokens=512, do_sample=True, top_k=50, top_p=0.95, temperature=0.3, repetition_penalty=1.3, eos_token_id=tokenizer.eos_token_id, bos_token_id = tokenizer.bos_token_id, pad_token_id = tokenizer.pad_token_id)
        rs = tokenizer.decode(generate_ids[0])
        predictions.append({
            "prompt": i,
            "answer": t,
            "prediction": rs
        })
        print(json.dumps({"prompt": i, "answer": t, "prediction": rs}, ensure_ascii=False, indent=4))
        print("\n\n")
    return predictions


if __name__ == "__main__":
    parser = HfArgumentParser(PredictionArguments)
    args = parser.parse_args_into_dataclasses()[0]
    model, tokenizer = get_trained_model_and_tokenizer(args.model_name_or_path, args.mode, args.tokenizer_fast)
    inputs, targets = get_datas(args.eval_dataset)
    predictions = generate_prediction(model, tokenizer, inputs, targets)
    json.dump(predictions, open(args.prediction_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
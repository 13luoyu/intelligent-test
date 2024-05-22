from peft import PeftConfig, PeftModel
from transformers import AutoTokenizer, AutoModelForCausalLM, HfArgumentParser, set_seed, BitsAndBytesConfig
import torch
import json
from dataclasses import dataclass, field
from typing import Optional



@dataclass
class PredictionArguments:
    model_name_or_path: Optional[str] = field(default=None, metadata={"help":"lora模型或base模型存储地址"})
    mode: Optional[str] = field(default=None, metadata={"help":"模型加载模式","choices":["lora", "base", "4bit-lora", "8bit-lora", "8bit-base"]})
    tokenizer_fast: Optional[bool] = field(default=None, metadata={"help":"是否使用快速tokenizer"})
    eval_dataset: Optional[str] = field(default=None, metadata={"help":"验证数据集地址"})
    prediction_file: Optional[str] = field(default=None, metadata={"help":"验证结果写入的文件"})
    seed: Optional[int] = field(default=None, metadata={"help":"随机种子值"})



def get_trained_model_and_tokenizer(model_name_or_path, mode, tokenizer_fast):
    """
    model_name_or_path: 模型存储的地址
    mode: 模型加载的模式
    tokenizer_fast: 是否使用fast tokenizer
    """
    if mode == "8bit-base":
        model = AutoModelForCausalLM.from_pretrained(model_name_or_path, torch_dtype=torch.float16, load_in_8bit=True, device_map='cuda:0' if torch.cuda.is_available() else 'auto', trust_remote_code=True, use_flash_attention_2=True)
        model.eval()
        tokenizer = AutoTokenizer.from_pretrained(model_name_or_path)

    elif mode == "8bit-lora":
        peft_config = PeftConfig.from_pretrained(model_name_or_path)
        # 加载base_model
        # bfloat16 的表示范围比 float16 更广，但是精度更低
        model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, return_dict=True, torch_dtype=torch.float16, device_map='cuda:0' if torch.cuda.is_available() else "auto", trust_remote_code=True, use_flash_attention_2=True, load_in_8bit=True)
        # 加载adapter_model
        model = PeftModel.from_pretrained(model, model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else 'auto')
        # tokenizer
        tokenizer = AutoTokenizer.from_pretrained(peft_config.base_model_name_or_path, use_fast=tokenizer_fast)
        model.eval()
    elif mode == "4bit-lora":
        bnb_config = BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_use_double_quant=True, bnb_4bit_quant_type="nf4", bnb_4bit_compute_dtype=torch.bfloat16)
        peft_config = PeftConfig.from_pretrained(model_name_or_path)
        model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else 'auto', torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True, quantization_config=bnb_config)
        model = PeftModel.from_pretrained(model, model_name_or_path, device_map="cuda:0" if torch.cuda.is_available() else "auto")
        model.eval()
        tokenizer = AutoTokenizer.from_pretrained(peft_config.base_model_name_or_path, use_fast=tokenizer_fast)
    elif mode == "lora":
        peft_config = PeftConfig.from_pretrained(model_name_or_path)
        model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else 'auto', torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True)
        model = PeftModel.from_pretrained(model, model_name_or_path, device_map="cuda:0" if torch.cuda.is_available() else "auto")
        model.eval()
        tokenizer = AutoTokenizer.from_pretrained(peft_config.base_model_name_or_path, use_fast=tokenizer_fast)
    elif mode == "base":
        model = AutoModelForCausalLM.from_pretrained(model_name_or_path, torch_dtype=torch.float16, device_map='cuda:0' if torch.cuda.is_available() else 'auto', trust_remote_code=True, use_flash_attention_2=True)
        model.eval()
        tokenizer = AutoTokenizer.from_pretrained(model_name_or_path)
    else:
        raise ValueError(f"未指定加载base model的模式 --mode, 必须为 \"base\", \"lora\", \"8bit-base\", \"8bit-lora\", \"4bit-lora\" 之一")
    
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
                i += line.split("Assistant:")[0] + "Assistant:"
                t += line.split("Assistant:")[1].replace(" ", "")
                stage = 2
            else:
                i += line
                stage = 1
        elif "</s>" in line:
            t += line
            inputs.append(i)
            targets.append(t)
            i, t = "", ""
            stage = 0
        elif stage == 1:
            i += line
        elif stage == 2:
            t += line
    return inputs, targets

def generate_prediction(model, tokenizer, inputs, targets):
    predictions = []
    for index in range(len(inputs)):
        print(f"### {index}")
        i = inputs[index]
        t = targets[index]
        input_ids = tokenizer([i], return_tensors="pt", add_special_tokens=False).input_ids
        if torch.cuda.is_available():
            input_ids = input_ids.to('cuda')
        # model.generate()参数
        # max_new_tokens (int, optional) - 生成的tokens的最大长度
        # do_sample (bool, optional, defaults to False) - 是否使用多项式采样解码，否则使用贪心解码。当设置为True采用多项式采样解码时，每次输出不同。如果设置为False，则top_k和top_p会被忽略。
        # temperature（float, optional, defaults to 1.0） - 控制生成的随机性。较高的值会增加文本的多样性和创造性，但可能会牺牲准确性和连贯性。具体地，如果设置为1，没有任何调整；设置值比1大，生成文本更加随机，因为会更平均地分配概率给各个token；设置值比1小，生成文本更加保守，会倾向于选择概率最高的token
        # top_k (int, optional, defaults to 50) - 单步中最多考虑的token数量
        # top_p (float, optional, defaults to 1.0) - 模型每步生成词库种每个词是下一个词的概率，概率按照由大到小排序，如果累计概率超过top_p，剩余的小概率词将不会被考虑。例如模型预测a:0.9, b:0.03, c:0.02, d: 0.01, ..., top_p=0.95，则只会考虑a, b, c
        # repetition_penalty (float, optional, defaults to 1.0) - 重复处罚的参数，用于缓解复读机（模型重复生成一句话）现象。1.0意味着没有惩罚。
        # generate_ids = model.generate(input_ids=input_ids, max_new_tokens=512, do_sample=True, top_k=50, top_p=0.95, temperature=0.3, repetition_penalty=1.3, eos_token_id=tokenizer.eos_token_id, bos_token_id = tokenizer.bos_token_id, pad_token_id = tokenizer.pad_token_id)
        model_inputs = {
            "input_ids": input_ids,
            "max_new_tokens": 512,
            "do_sample": False,
            "top_k": 50,
            "top_p": 1.0,
            "temperature": 1.0,
            "repetition_penalty": 1.0
        }
        generate_ids = model.generate(**model_inputs)
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
    if args.seed is not None:
        set_seed(args.seed)
    model, tokenizer = get_trained_model_and_tokenizer(args.model_name_or_path, args.mode, args.tokenizer_fast)
    inputs, targets = get_datas(args.eval_dataset)
    predictions = generate_prediction(model, tokenizer, inputs, targets)
    json.dump(predictions, open(args.prediction_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
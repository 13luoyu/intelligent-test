from peft import PeftConfig, PeftModel
from transformers import AutoConfig, AutoTokenizer, AutoModelForCausalLM, HfArgumentParser, BitsAndBytesConfig
import torch
from dataclasses import dataclass, field
from typing import Optional


# 合并base和lora模型并保存
# python merge.py --adapter_model_name ./output/llama2_lora_dev_dev_acc0_9792 --output_name ./output/llama2_dev_dev_acc0_9792 --mode 4bit

@dataclass
class PredictionArguments:
    adapter_model_name: Optional[str] = field(default=None, metadata={"help":"lora模型存储的地址"})
    output_name: Optional[str] = field(default=None, metadata={"help":"合并后的模型保存目录"})
    mode: Optional[str] = field(default=None, metadata={"help":"加载base model的模式", "choices": ['4bit', '8bit']})



def merge_model(adapter_model_name, output_name, mode):
    """
    将base_model和adapter_model合并，并返回
    adapter_model_name: adapter_model的路径
    output_name: 合并后模型保存的路径，如果为None则不保存
    """
    peft_config = PeftConfig.from_pretrained(adapter_model_name)
    # 加载base_model
    # bfloat16 的表示范围比 float16 更广，但是精度更低
    if mode == "4bit":
        bnb_config = BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_use_double_quant=True, bnb_4bit_quant_type="nf4", bnb_4bit_compute_dtype=torch.bfloat16)
        model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, return_dict=True, torch_dtype=torch.float16, device_map='cuda:0' if torch.cuda.is_available() else "auto", trust_remote_code=True, use_flash_attention_2=True, quantization_config=bnb_config)
    elif mode == "8bit":
        model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, return_dict=True, torch_dtype=torch.float16, device_map='cuda:0' if torch.cuda.is_available() else "auto", trust_remote_code=True, use_flash_attention_2=True, load_in_8bit=True)
    else:
        model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, return_dict=True, torch_dtype=torch.float16, device_map='cuda:0' if torch.cuda.is_available() else "auto", trust_remote_code=True, use_flash_attention_2=True)
    # 加载adapter_model
    model = PeftModel.from_pretrained(model, adapter_model_name, device_map={"":0})
    # tokenizer
    tokenizer = AutoTokenizer.from_pretrained(peft_config.base_model_name_or_path)
    # config
    config = AutoConfig.from_pretrained(peft_config.base_model_name_or_path)
    architecture = config.architectures[0]
    print("模型结构", architecture)
    model = model.merge_and_unload()
    model.eval()
    # 合并adapter_model
    model.save_pretrained(output_name)
    tokenizer.save_pretrained(output_name)



if __name__ == "__main__":
    parser = HfArgumentParser(PredictionArguments)
    args = parser.parse_args_into_dataclasses()[0]
    merge_model(args.adapter_model_name, args.output_name, args.mode)
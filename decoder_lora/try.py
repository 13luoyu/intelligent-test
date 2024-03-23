import torch
from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig
from peft import PeftConfig, PeftModel


def try1():
    device_map = "cuda:0" if torch.cuda.is_available() else "auto"
    model = AutoModelForCausalLM.from_pretrained('./output/best_model_full_dev_dev_acc0_9792',device_map=device_map,torch_dtype=torch.float16,load_in_8bit=True,trust_remote_code=True,use_flash_attention_2=True)
    model.eval()
    tokenizer = AutoTokenizer.from_pretrained('./output/best_model_full_dev_dev_acc0_9792',use_fast=False)
    tokenizer.pad_token = tokenizer.eos_token

    input_ids = tokenizer(['<s>Human: 除本所另有规定外，本所对不同交易方式下的债券交易时间安排如下：(一)采用匹配成交方式的，每个交易日的9:15至9:25为开盘集合匹配时间，9:30至11:30、13:00至15:30为连续匹配时间；(二)采用点击成交、询价成交和协商成交方式的，交易时间为每个交易日的9:00至11:30、13:00至20:00；(三)采用竞买成交方式的，每个交易日的9:00至10:00为卖方提交竞买发起申报时间，10:00至11:30为应价方提交应价申报时间。\n</s><s>Assistant: '], return_tensors="pt", add_special_tokens=False).input_ids

    if torch.cuda.is_available():
        input_ids = input_ids.to('cuda')

    # generate_input = {
    #     "input_ids":input_ids,
    #     "max_new_tokens":512,
    #     "do_sample":True,
    #     "top_k":50,
    #     "top_p":0.95,
    #     "temperature":0.3,
    #     "repetition_penalty":1.3,
    #     "eos_token_id":tokenizer.eos_token_id,
    #     "bos_token_id":tokenizer.bos_token_id,
    #     "pad_token_id":tokenizer.pad_token_id
    # }
    generate_input = {
        "input_ids": input_ids
    }

    generate_ids  = model.generate(**generate_input)
    text = tokenizer.decode(generate_ids[0])
    print(text)



def try2():
    device_map = "cuda:0" if torch.cuda.is_available() else "auto"
    bnb_config = BitsAndBytesConfig(
        load_in_4bit=True,  # 4位量化
        bnb_4bit_use_double_quant=True,  # 此标志用于嵌套量化，其中第一次量化的量化常数再次量化
        bnb_4bit_quant_type="nf4",  # 设置 bnb.nn.Linear4Bit 层中的量化数据类型。选项是 FP4 和 NF4 数据类型，由 fp4 或 nf4 指定。
        bnb_4bit_compute_dtype=torch.bfloat16  # 设置计算类型
    )
    adapter_model_name_or_path = './output/best_model_dev_dev_acc0_9792'
    
    peft_config = PeftConfig.from_pretrained(adapter_model_name_or_path)
    model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, device_map=device_map,torch_dtype=torch.float16,load_in_8bit=False,trust_remote_code=True,use_flash_attention_2=True, quantization_config=bnb_config)
    model = PeftModel.from_pretrained(model, adapter_model_name_or_path, device_map=device_map)
    model.eval()
    tokenizer = AutoTokenizer.from_pretrained(peft_config.base_model_name_or_path,use_fast=False)
    tokenizer.pad_token = tokenizer.eos_token

    input_ids = tokenizer(['<s>Human: 给出一条规则，请你尽可能全面地将规则中的关键信息抽取出来。\n规则: 除本所另有规定外，本所对不同交易方式下的债券交易时间安排如下：(一)采用匹配成交方式的，每个交易日的9:15至9:25为开盘集合匹配时间，9:30至11:30、13:00至15:30为连续匹配时间；(二)采用点击成交、询价成交和协商成交方式的，交易时间为每个交易日的9:00至11:30、13:00至20:00；(三)采用竞买成交方式的，每个交易日的9:00至10:00为卖方提交竞买发起申报时间，10:00至11:30为应价方提交应价申报时间。\n</s><s>Assistant: '], return_tensors="pt", add_special_tokens=False).input_ids

    if torch.cuda.is_available():
        input_ids = input_ids.to('cuda')

    # generate_input = {
    #     "input_ids":input_ids,
    #     "max_new_tokens":512,
    #     "do_sample":True,
    #     "top_k":50,
    #     "top_p":0.95,
    #     "temperature":0.3,
    #     "repetition_penalty":1.3,
    #     "eos_token_id":tokenizer.eos_token_id,
    #     "bos_token_id":tokenizer.bos_token_id,
    #     "pad_token_id":tokenizer.pad_token_id
    # }
    generate_input = {
        "input_ids": input_ids
    }

    generate_ids  = model.generate(**generate_input)
    text = tokenizer.decode(generate_ids[0])
    print(text)




if __name__ == "__main__":
    try1()
    # try2()
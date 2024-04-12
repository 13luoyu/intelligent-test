import json
from transformers import AutoTokenizer, AutoModelForCausalLM, BitsAndBytesConfig
from peft import PeftConfig, PeftModel
import torch
from transfer.knowledge_tree import encode_tree
from ours.process_tci_to_tco import token_classification_with_algorithm




def token_classification(tci, model_name_or_path, knowledge, print_log=False, use_algorithm=False):
    bnb_config = BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_use_double_quant=True, bnb_4bit_quant_type="nf4", bnb_4bit_compute_dtype=torch.bfloat16)
    device_map = "cuda:0" if torch.cuda.is_available() else "auto"

    peft_config = PeftConfig.from_pretrained(model_name_or_path)
    model = AutoModelForCausalLM.from_pretrained(peft_config.base_model_name_or_path, device_map=device_map, torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True, quantization_config=bnb_config)
    model = PeftModel.from_pretrained(model, model_name_or_path, device_map=device_map)
    model.eval()
    tokenizer = AutoTokenizer.from_pretrained(peft_config.base_model_name_or_path, use_fast=False)

    tco = tci.copy()
    for index, rule in enumerate(tco):
        if print_log:
            print(f"Token classification: {index+1}/{len(tco)}")
        input_ids = tokenizer([f"<s>Human:给出一条规则，请你尽可能全面地将规则中的关键信息抽取出来。\n规则:{rule['text']}\n</s><s>Assistant:"], return_tensors="pt", add_special_tokens=False).input_ids
        if torch.cuda.is_available():
            input_ids = input_ids.to('cuda')
        generate_input = {
            "input_ids": input_ids
        }
        generate_ids = model.generate(**generate_input)
        label = tokenizer.decode(generate_ids[0]).split("Assistant:")[-1].split("</s>")[0].strip()
        rule['label'] = label
    
    if use_algorithm:
        # 将label转换为BIO格式
        for data in tco:
            text, label = data['text'].replace("：", ":"), data['label'].replace("：", ":").replace(" ", "")
            new_label = ["O"] * len(text)
            p = -1
            for lb in label.split(","):
                a, b = lb.split(":")[0], ":".join(lb.split(":")[1:])
                p = text.find(b, p+1)
                if p == -1:
                    continue
                new_label[p:p+len(b)] = ["B-" + a] + ["I-" + a] * (len(b)-1)
            data['label'] = " ".join(new_label)

        tco = token_classification_with_algorithm(tco, knowledge)

    return tco


if __name__ == "__main__":
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json", "r", encoding="utf-8"))

    tci_data = json.load(open("cache/tci.json", "r", encoding="utf-8"))
    tco_data = token_classification(tci_data, "../model/trained/llama2_rule_element_extraction_v2", knowledge, print_log=True)
    json.dump(tco_data, open("cache/tco.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

import json

def generate_llm_chat_data_for_ir_v2(datas):
    s = "\"text\"\n"
    for data in datas:
        prompt = data['prompt']
        system, user = prompt.split("\n")[0], "\n".join(prompt.split("\n")[1:])
        s += f"\"<|begin_of_text|><|start_header_id|>system<|end_header_id|>\n\n你是一个金融科技领域的专家。{system}<|eot_id|><|start_header_id|>user<|end_header_id|>\n\n{user}<|eot_id|><|start_header_id|>assistant<|end_header_id|>\n\n{data['answer']}<|eot_id|><|end_of_text|>\"\n"
    return s


def main_v2():
    # 读取标注好的信息抽取数据，生成训练集和验证集
    datas = json.load(open("../data/data_for_LLM_v2/ir_annotation_v2.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v2/llama3/ir_all_v2.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v2/ir_train_v2.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v2/llama3/ir_train_v2.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v2/ir_validate_v2.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v2/llama3/ir_validate_v2.csv", "w", encoding="utf-8") as f:
        f.write(s)
    
    datas = json.load(open("../data/data_for_LLM_v2/assemble_annotation_v2.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v2/llama3/assemble_all_v2.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v2/assemble_train_v2.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v2/llama3/assemble_train_v2.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v2/assemble_validate_v2.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v2/llama3/assemble_validate_v2.csv", "w", encoding="utf-8") as f:
        f.write(s)
    



def main_v3():
    datas = json.load(open("../data/data_for_LLM_v3/ir_assemble_annotation_v3.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v3/llama3/ir_assemble_all_v3.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v3/ir_assemble_train_v3.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v3/llama3/ir_assemble_train_v3.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v3/ir_assemble_validate_v3.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v3/llama3/ir_assemble_validate_v3.csv", "w", encoding="utf-8") as f:
        f.write(s)


def main_v4():
    datas = json.load(open("../data/data_for_LLM_v4/train_v4.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v4/llama3/train_v4.csv", "w", encoding="utf-8") as f:
        f.write(s)
    datas = json.load(open("../data/data_for_LLM_v4/validate_v4.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir_v2(datas)
    with open("../data/data_for_LLM_v4/llama3/validate_v4.csv", "w", encoding="utf-8") as f:
        f.write(s)




if __name__ == "__main__":
    main_v2()
    main_v3()
    # main_v4()
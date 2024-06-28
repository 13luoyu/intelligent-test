import json


def read_OBI_to_rule(texts, labels):
    """
    读取模型输出的OBI文件，将其转化为key-value对的形式，存放在stack中。同时记录句子中的；和。并记录在sentence_separate_1和sentence_separate_2中

    :param texts: 一段自然语言
    :param labels: texts对应的标签序列，以空格分隔的字符串形式呈现
    :return stack: 按照出现顺序记录text-label对的数组
    :return sentence_separate_1: 记录；之后的下一个{label:text}在stack中的位置
    :return sentence_separate_2: 记录。之后的下一个{label:text}在stack中的位置
    """
    stack = []  # 按顺序记录所有的label及其对应text为{label:text}
    a, b = 0, 0  # a, b为一个text在句子中的开始和结束位置
    last_label = "O"
    for i, label in enumerate(labels.split(" ")):
        if label == "O":  # O->O, B->O, I->O
            if last_label != "O":  # B->O, I->O
                b = i
                # 记录到stack中
                stack.append({last_label: texts[a:b]})
            last_label = label
        else:
            l_content = label[2:]
            if "B" == label[0]:  # O->B，I->B，B->B
                # 处理旧标签
                if last_label != "O":
                    b = i
                    # 记录到stack中
                    stack.append({last_label: texts[a:b]})
                # 记录新标签
                a = i
                last_label = l_content
            else:  # 如果是... -> I
                ...
    
    return stack


def generate_llm_chat_data_for_ir(rules):
    s = "\"text\"\n"
    for rule in rules:
        s += "\"<s>Human: 给出一条规则，请你尽可能全面地将规则中的关键信息抽取出来。\n规则: "
        s += rule['text']
        s += "\n</s><s>Assistant: "
        stack = read_OBI_to_rule(rule['text'], rule['label'])
        stack = str(stack).replace("[", "").replace("]", "").replace("{", "").replace("}", "").replace("'", "").replace(" ", "")
        s += stack
        s += "\n</s>\"\n"
    return s


if __name__ == "__main__":
    rules = json.load(open("../data/data_for_LLM_encoder/tc_train_data_rules.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir(rules)
    with open("../data/data_for_LLM_decoder/ir_train.csv", "w", encoding="utf-8") as f:
        f.write(s)
    rules = json.load(open("../data/data_for_LLM_encoder/tc_validate_data_rules.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir(rules)
    with open("../data/data_for_LLM_decoder/ir_validate.csv", "w", encoding="utf-8") as f:
        f.write(s)
    rules = json.load(open("../data/data_for_LLM_encoder/rules.json", "r", encoding="utf-8"))
    s = generate_llm_chat_data_for_ir(rules)
    with open("../data/data_for_LLM_decoder/ir_all.csv", "w", encoding="utf-8") as f:
        f.write(s)

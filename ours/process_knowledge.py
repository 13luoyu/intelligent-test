import json
from pprint import pprint
import os

def process_knowledge(rules):
    todo_text = []
    knowledge = {}
    divided_words = ["、", "以及", "和", "或者", "或"]
    knowledge_count, cannot_process = 0, 0
    for rule in rules:
        if rule["type"] == "2":
            knowledge_count += 1
            text = rule["text"]
            text = text.replace("（", "(")
            text = text.replace("）", ")")
            unuse_words = ["可以", "应当"]
            for word in unuse_words:
                text = text.replace(word, "")
            # 关键词：是（是指），包括
            if "包括" in text:
                if "下列" in text:
                    label = text.split("包括")[0]
                    content = text.split("包括")[1]
                    if ")" in content:
                        contents = [c.split(")")[1] for c in content.split("；")]
                    else:
                        contents = content[:content.find("等")]
                        contents = [content]
                        new_c = []
                        for word in divided_words:
                            for c in contents:
                                cs = c.split(word)
                                for ci in cs:
                                    if ci not in new_c:
                                        new_c.append(ci)
                                        if c in new_c and ci != c and (ci in c or c in ci):
                                            new_c.remove(c)
                            contents = new_c
                    knowledge[label] = contents
                else:
                    label = text.split("包括")[0]
                    content = text.split("包括")[1]
                    if "等" in content:
                        content = content[:content.find("等")]
                    if "：" in content:
                        content = content[content.find("：") + 1:]
                    if "；" in content:
                        contents = content.split("；")
                    elif "、" in content:
                        contents = content.split("、")
                    else:
                        contents = content.split("和")
                    knowledge[label] = contents
            elif ("是" in text or "指" in text or "为" in text) and text[0] != "(":
                if "是" in text:
                    texts = text.split("；")
                    label = ""
                    for text in texts:
                        if "是" not in text and label != "":
                            knowledge[label] = knowledge[label] + "；" + text
                        elif "是" in text:
                            label = text.split("是")[0]
                            content = text.split("是")[1]
                            if "指" in content:
                                content = content[content.find("指") + 1:]
                            knowledge[label] = content
                elif "指" in text:
                    texts = text.split("；")
                    for text in texts:
                        label = text.split("指")[0]
                        if label[0] == "(":
                            label = label.split(")")[1]
                        content = text.split("指")[1]
                        knowledge[label] = content
                else:  # 为
                    texts = text.split("；")
                    label = ""
                    for text in texts:
                        if "指" not in text and label != "":
                            knowledge[label] = knowledge[label] + "；" + text
                        elif "指" in text:
                            label = text.split("为")[0]
                            content = text.split("为")[1]
                            if "：" in content:
                                content = content[content.find("：") + 1:]
                            knowledge[label] = content
            elif text[0] == "(":
                if "：" in text:
                    label = text.split("：")[0]
                    label = label[label.find(")") + 1:]
                    content = text.split("：")[1]
                else:
                    label = text.split("，")[0]
                    label = label[label.find(")") + 1:]
                    content = "，".join(text.split("：")[1:])
                knowledge[label] = content
            elif "采用" in text:
                if "：" in text:
                    label = text.split("：")[0]
                    label = label.replace("采用", "")
                    content = text.split("：")[1]
                    contents = [c.split(")")[1] for c in content.split("；")]
                    knowledge[label] = contents
                else:
                    if text.find("采用") == 0:
                        text = text[2:]
                    label = text.split("采用")[0]
                    content = text.split("采用")[1]
                    if "其他" in content:
                        t = content[content.find("其他") + 2:-1]
                        label = label + t
                    elif "等" in content:
                        t = content[content.find("等") + 1:-1]
                        label = label + t
                    elif "种" in content:
                        t = content[content.find("种") + 1:-1]
                        label = label + t
                    contents = [content]
                    new_c = []
                    for word in divided_words:
                        for c in contents:
                            cs = c.split(word)
                            for ci in cs:
                                if ci not in new_c:
                                    new_c.append(ci)
                                    if c in new_c and ci != c and (ci in c or c in ci):
                                        new_c.remove(c)
                        contents = new_c
                    knowledge[label] = contents
            else:
                todo_text.append(text)
                cannot_process += 1
    return knowledge, "\n".join(todo_text), knowledge_count, cannot_process


if __name__ == "__main__":
    # 第一个参数为模型的输出文件，第二个为领域知识保存文件，第三个为算法无法自动处理，需要手动处理的领域知识原文保存文件。
    # 算法处理后，需要人工核对
    # process_knowledge("rules_cache/sco.json", "rules_cache/knowledge.json", "rules_cache/todo_knowledge.json")

    knowledge_file, todo_knowledge_file = "rules_cache/knowledge.json", "rules_cache/todo_knowledge.txt"
    all_knowledge = []
    todo_fp = open(todo_knowledge_file, "w" ,encoding="utf-8")
    if os.path.exists(knowledge_file):
        os.remove(knowledge_file)
    if os.path.exists(todo_knowledge_file):
        os.remove(todo_knowledge_file)
    a, b = 0, 0
    for file in os.listdir("../data/业务规则/json_for_sequence_classification/"):
        if "finish" in file:
            rules = json.load(open("../data/业务规则/json_for_sequence_classification/" + file, "r", encoding="utf-8"))
            knowledge, todo_text, knowledge_count, cannot_process = process_knowledge(rules)
            a += knowledge_count
            b += cannot_process
            all_knowledge += knowledge
            todo_fp.write(todo_text)
            todo_fp.write("\n")
    json.dump(all_knowledge, open(knowledge_file, "w", encoding="utf-8"))
    todo_fp.close()
    print(f"所有领域知识数目：{a}, 能够处理的数目：{a-b}, 处理率为{round(float(a-b)/float(a)*100.0, 1)}%")
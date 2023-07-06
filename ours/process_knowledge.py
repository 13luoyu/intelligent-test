import json
from pprint import pprint
import os

def process_knowledge(input_file: str, output_file: str, todo_file: str):
    todo_fp = open(todo_file, "a", encoding="utf-8")
    knowledge = {}
    rules = json.load(open(input_file, "r", encoding="utf-8"))
    divided_words = ["、", "以及", "和", "或者", "或"]
    for rule in rules:
        if rule["type"] == "2":
            text = rule["text"]
            unuse_words = ["可以", "应当"]
            for word in unuse_words:
                text = text.replace(word, "")
            # 关键词：是（是指），包括
            if "包括" in text:
                if "下列" in text:
                    label = text.split("包括")[0]
                    content = text.split("包括")[1]
                    contents = [c.split(")")[1] for c in content.split("；")]
                    knowledge[label] = contents
                else:
                    label = text.split("包括")[0]
                    content = text.split("包括")[1]
                    if "等" in content:
                        content = content[:content.find("等")]
                    if "：" in content:
                        content = content[content.find("：") + 1:]
                    if "、" in content:
                        contents = content.split("、")
                    else:
                        contents = content.split("和")
                    knowledge[label] = contents
            elif ("是" in text or "指" in text or "为" in text) and text[0] != "(":
                if "是" in text:
                    texts = text.split("；")
                    for text in texts:
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
                    for text in texts:
                        label = text.split("为")[0]
                        content = text.split("为")[1]
                        if "：" in content:
                            content = content[content.find("：") + 1:]
                        knowledge[label] = content
            elif text[0] == "(":
                label = text.split("：")[0]
                label = label[label.find(")") + 1:]
                content = text.split("：")[1]
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
                todo_fp.write(text + "\n")
    # pprint(knowledge)
    if os.path.exists(output_file):
        knowledge_pre = json.load(open(output_file, "r", encoding="utf-8"))
        knowledge.update(knowledge_pre)
    json.dump(knowledge, open(output_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)




if __name__ == "__main__":
    # 第一个参数为模型的输出文件，第二个为领域知识保存文件，第三个为算法无法自动处理，需要手动处理的领域知识原文保存文件。
    # 算法处理后，需要人工核对
    process_knowledge("rules_cache/sco.json", "rules_cache/knowledge.json", "rules_cache/todo_knowledge.json")
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
            p1, p2, p3, p4 = text.find("包括"), text.find("是"), text.find("指"), text.find("为")
            
            if "计算公式" in text:
                text = text.replace("＝", "=")
                label = text.split("：")[-1].split("=")[0]
                content = "=".join(text.split("=")[1:])
                knowledge[f"{label}的计算公式"] = content
            elif "“元”" in text or "四舍五入" in text or "=" in text or "红筹公司" in text:
                continue

            # 特殊处理
            elif text[0] == "(" or "含义" in text:
                if "：" in text:
                    if "含义" in text:
                        if text.count("：") >= 2:
                            label = text.split("：")[-2]
                            label = label[label.find(")") + 1:]
                            content = text.split("：")[-1]
                        else:
                            label = text.split("：")[-1].split("，")[0]
                            label = label[label.find(")") + 1:]
                            content = text.split("：")[-1].split("，")[-1]
                    else:
                        label = text.split("：")[0]
                        label = label[label.find(")") + 1:]
                        content = text.split("：")[1]
                    if content[0] == "指":
                        content = content[1:]
                    elif content[:2] == "是指":
                        content = content[2:]
                    if content[0] == "即":
                        content = content[1:]
                elif ":" in text:
                    if "含义" in text:
                        if text.count(":") >= 2:
                            label = text.split(":")[-2]
                            label = label[label.find(")") + 1:]
                            content = text.split(":")[-1]
                        else:
                            label = text.split(":")[-1].split("，")[0]
                            label = label[label.find(")") + 1:]
                            content = text.split(":")[-1].split("，")[-1]
                    else:
                        label = text.split(":")[0]
                        label = label[label.find(")") + 1:]
                        content = text.split(":")[1]
                    if content[0] == "指":
                        content = content[1:]
                    elif content[:2] == "是指":
                        content = content[2:]
                    if content[0] == "即":
                        content = content[1:]
                else:
                    label = text.split("，")[0]
                    label = label[label.find(")") + 1:]
                    content = "，".join(text.split("，")[1:])
                    if content[0] == "指":
                        content = content[1:]
                    elif content[:2] == "是指":
                        content = content[2:]
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
                        if text.count("是")>=2:
                            todo_text.append(text)
                            continue
                        text = text[2:]
                    label = text.split("采用")[0]
                    content = text.split("采用")[1]
                    if label[-1] == "，":
                        label = label[:-1]
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
            
            # 分类型
            elif p1 != -1 and ((p2 == -1 or p2 != -1 and p1 < p2) or (p3 == -1 or p3 != -1 and (p1 < p3 or text.find("指令")== p3)) or (p4 == -1 or p4 != -1 and p1 < p4)):
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
                    if label[-1] == "应":
                        label = label[:-1]
                    elif label[-2:] == "应该":
                        label = label[:-2]
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
                    new_contents = []
                    ci = ""
                    for c in contents:
                        if "(" in c and ")" not in c:
                            ci += c
                        elif ")" in c and "(" not in c:
                            ci += c
                            new_contents.append(ci)
                            ci = ""
                        elif ci != "":
                            ci += c
                        else:
                            # (一)...(二)...的处理
                            if c[0] == "(" and ")" in c:
                                c = c[c.find(")")+1:]
                            new_contents.append(c)
                    contents = new_contents
                    knowledge[label] = contents
            
            # 解释型
            elif (p2 != -1 or p3 != -1 or p4 != -1) and text[0] != "(":
                if p2 != -1 and (p3 == -1 or p3 != -1 and p2 < p3) and (p4 == -1 or p4 != -1 and p2 < p4):
                    texts = text.split("；")
                    label = ""
                    for text in texts:
                        if "是" not in text and label != "":
                            knowledge[label] = knowledge[label] + "；" + text
                        elif "是" in text:
                            label = text.split("是")[0]
                            content = text.split("是")[1]
                            if "含义" in label:
                                if "：" in label:
                                    label = label.split("：")[-1]
                                if ")" in label:
                                    label = label.split(")")[-1]
                            if "指" in content:
                                content = content[content.find("指") + 1:]
                            knowledge[label] = content
                elif p3 != -1 and (p2 == -1 or p2 != -1 and p3 < p2) and (p4 == -1 or p4 != -1 and p3 < p4) and text.find("指定") != p3 and text.find("指引") != p3:
                    texts = text.split("；")
                    for text in texts:
                        label = text.split("指")[0]
                        if label[0] == "(":
                            label = label.split(")")[1]
                        if label[-1] == "：":
                            label = label[:-1]
                        content = text.split("指")[1]
                        knowledge[label] = content
                elif p4 != -1 and (p2 == -1 or p2 != -1 and p4 < p2) and (p3 == -1 or p3 != -1 and p4 < p3):  # 为
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
            
            elif "下列" in text:
                if "下列类型的" in text:
                    label = text.split("下列类型的")[-1].split("：")[0]
                    content = text.split("：")[-1]
                    contents = content.split("；")
                    for i, c in enumerate(contents):
                        if c[0] == "(" and ")" in c:
                            contents[i] = c[c.find(")")+1:]
                    knowledge[label] = contents
                else:
                    label = text.split("下列")[-1].split("：")[0]
                    content = text.split("：")[-1]
                    contents = content.split("；")
                    for i, c in enumerate(contents):
                        if c[0] == "(" and ")" in c:
                            contents[i] = c[c.find(")")+1:]
                    knowledge[label] = contents

            else:
                todo_text.append(text)
                cannot_process += 1
    
    for key in list(knowledge.keys()):
        if isinstance(knowledge[key], str):
            if knowledge[key][-1] == "。":
                knowledge[key] = knowledge[key][:-1]
            if key[-1] == "，":
                knowledge[key[:-1]] = knowledge[key]
                del knowledge[key]
        else:
            for i, k in enumerate(knowledge[key]):
                if k[-1] == "。":
                    knowledge[key][i] = k[:-1]
            if key[-1] == "，":
                knowledge[key[:-1]] = knowledge[key]
                del knowledge[key]
    return knowledge, "\n".join(todo_text), knowledge_count, cannot_process


if __name__ == "__main__":
    # 第一个参数为模型的输出文件，第二个为领域知识保存文件，第三个为算法无法自动处理，需要手动处理的领域知识原文保存文件。
    # 算法处理后，需要人工核对
    # process_knowledge("cache/sco.json", "cache/knowledge.json", "cache/todo_knowledge.json")

    knowledge_file, todo_knowledge_file = "cache/knowledge.json", "cache/todo_knowledge.txt"
    all_knowledge = {}
    todo_fp = open(todo_knowledge_file, "w" ,encoding="utf-8")
    a, b = 0, 0
    for file in os.listdir("../data/business_rules/annotation_for_sequence_classification/"):
        if "finish" in file:
            rules = json.load(open("../data/business_rules/annotation_for_sequence_classification/" + file, "r", encoding="utf-8"))
            knowledge, todo_text, knowledge_count, cannot_process = process_knowledge(rules)
            a += knowledge_count
            b += cannot_process
            all_knowledge = {**all_knowledge, **knowledge}
            todo_fp.write(todo_text)
            todo_fp.write("\n")
    json.dump(all_knowledge, open(knowledge_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    todo_fp.close()
    print(f"所有领域知识数目：{a}, 能够处理的数目：{a-b}, 处理率为{round(float(a-b)/float(a)*100.0, 1)}%")
import pdfplumber
import json
import os

# 读取一个目录，按照句号分割，生成sequence_classification文件

def is_id(str):
    # 判断一句话是否是id开头
    str = str.split(" ")[0].strip()
    if str == "":
        return False
    if str[0]=="第" and "条" in str:
        return True
    if "." not in str:
        return False
    ids = str.split(".")
    for id in ids:
        if not id.isdigit():
            return False
    return True

def read_pdf_to_txt(pdf_file):
    """
    读取并解析pdf文件，将其转化为按照id划分的一个个句子
    pdf_file: 要读取的pdf文件
    ts: 一个字符串，按照id划分的句子之间以"\\n"区分
    """
    s = ""
    with pdfplumber.open(pdf_file) as pdf:
        for page in pdf.pages:
            s += f"{page.extract_text()}\n"
    ts = ""
    for i, line in enumerate(s.split("\n")):
        # 每个line是pdf文档中的一行，但是可能有多个句子
        # 什么时候换行呢？
        # 如果是标题、附件等，换行；如果是一个规则的开始（遇到id），则换行
        line = line.strip()
        if line[0:2] == "附件":  # 通常是一篇文档的开始
            if len(line) == 2:
                ts += "\n" + line + "\n"
                continue
            elif line.replace(" ","")[2] == "：" or line.replace(" ","")[2] == ":" or line.replace(" ","")[2].isdigit():  # 附件：、附件:、附件1...
                ts += "\n" + line.replace(" ","") + "\n"
                continue
        if line == "" or line[0] == "—" and line[-1] == "—" or line.isdigit():  # 忽略空行和页码
            continue
        if "修订）" == line[-3:]:  # 可能出现在标题中
            ts += line + "\n"
            continue
        if line[0] == "第" and " " in line and ("章" in line or "节" in line) and line.find(" ") > max(line.find("章"), line.find("节")):  # 章节标题
            ts += "\n" + line + "\n"
        elif is_id(line) and ts[-1] == "。":  # 遇到1.1.1这样的
            ts += "\n" + line
        else:  # 标题或未结束的一句正文
            ts += line

    # with open("tmp.txt", "a+", encoding="utf-8") as f:
    #     f.write(ts)
    return ts



def read_txt_to_json(txt_data):
    '''
    将txt_data按句划分，写成sci的json格式
    txt_data: 输入数据
    data: 返回的sci数据
    '''
    data = []
    lines = txt_data.split("\n")
    for line in lines:
        if line.strip() == "":
            continue
        line = line.strip().replace("：", ":").replace("︰", ":")
        id = line.split(" ")[0]
        if is_id(id):
            text = "".join(line.split(" ")[1:])
            text = text.replace("。", "。\n")
            texts = text.split("\n")
            for index, text in enumerate(texts):
                if text.strip() != "":
                    d = {"text": text.strip(), "label": "", "type": "", "id": f"{id}_{index}"}
                    data.append(d)
        else:
            text = line.replace("。", "。\n")
            texts = text.split("\n")
            for index, text in enumerate(texts):
                if text.strip() != "":
                    d = {"text": text.strip(), "label": "", "type": ""}
                    data.append(d)
    
    return data





if __name__ == "__main__":
    for file in os.listdir("../data/business_rules/origin"):
        if "pdf" in file:
            txt_data = read_pdf_to_txt(f"../data/business_rules/origin/{file}")
            with open(f"../data/business_rules/txt/{file[:-4]}.txt", "w", encoding="utf-8") as f:
                f.write(txt_data)
    
    for file in os.listdir("../data/business_rules/txt"):
        txt_data = open(f"../data/business_rules/txt/{file[:-4]}.txt", "r", encoding="utf-8").read()
        sci = read_txt_to_json(txt_data)
        json.dump(sci, open(f"../data/business_rules/annotation_for_sequence_classification/{file[:-4]}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

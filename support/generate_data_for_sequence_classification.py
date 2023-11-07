import pdfplumber
import json
import os

# 读取一个目录，按照句号分割，生成sequence_classification文件

def is_id(str):
    # 判断一句话是否是id开头
    str = str.split(" ")[0]
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
        # 什么时候换行呢？
        # 如果是标题、附件等，换行；如果是一个规则的开始（遇到id），则换行
        line = line.strip().replace("：", ":").replace("︰", ":")
        if line[0:2] == "附件":
            if len(line) == 2:
                ts += "\n" + line + "\n"
                continue
            elif line.replace(" ","")[2] == ":" or line.replace(" ","")[2].isdigit():
                ts += "\n" + line.replace(" ","") + "\n"
                continue
        if line == "":
            continue
        if "修订）" == line[-3:]:
            ts += line + "\n"
            continue
        if line[0] == "第" and " " in line and ("章" in line or "节" in line):  # 章节标题
            ts += "\n" + line + "\n"
        elif is_id(line) and ts[-1] == "。":  # 遇到1.1.1这样的
            ts += "\n" + line
        elif line[0] == "—" and line[-1] == "—":
            continue
        else:
            ts += line

    return ts



def read_txt_to_json(txt_data):
    '''
    将txt_data按句划分，写成sci的json格式
    txt_data: 输入数据
    data: 返回的sci数据
    '''
    data = []
    # with open(txt_file, "r", encoding="utf-8") as f:
    #     lines = f.readlines()
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
    # txt_data = read_pdf_to_txt(f"../data/上海证券交易所债券交易规则.pdf")
    # with open(f"../data/上海证券交易所债券交易规则.txt", "w", encoding="utf-8") as f:
    #     f.write(txt_data)
    # sci = read_txt_to_json(txt_data)
    # json.dump(sci, open(f"../data/上海证券交易所债券交易规则.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    # exit(0)
    for file in os.listdir("../data/业务规则/origin"):
        if "pdf" in file:
            txt_data = read_pdf_to_txt(f"../data/业务规则/origin/{file}")
            with open(f"../data/业务规则/txt/{file[:-4]}.txt", "w", encoding="utf-8") as f:
                f.write(txt_data)
    
    for file in os.listdir("../data/业务规则/txt"):
        txt_data = open(f"../data/业务规则/txt/{file[:-4]}.txt", "r", encoding="utf-8").readlines()
        sci = read_txt_to_json(txt_data)
        json.dump(sci, open(f"../data/业务规则/json_for_sequence_classification/{file[:-4]}.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

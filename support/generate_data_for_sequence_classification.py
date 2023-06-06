import pdfplumber
import json
import os


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

# 读取pdf，将其写入一个txt文件中
def read_pdf_to_txt(pdf_file, txt_file):
    s = ""
    with pdfplumber.open(pdf_file) as pdf:
        for page in pdf.pages:
            s += f"{page.extract_text()}\n"
    ts = ""
    for i, line in enumerate(s.split("\n")):
        # 什么时候换行呢？
        # 如果是标题、附件等，换行；如果是一个规则的开始（遇到id），则换行
        line = line.strip()
        if line[0:2] == "附件":
            if len(line) == 2:
                ts += "\n" + line + "\n"
                continue
            elif line.replace(" ","")[2] == "：" or line.replace(" ","")[2] == ":" or line.replace(" ","")[2].isdigit():
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

    with open(txt_file, "w+", encoding="utf-8") as f:
        f.write(ts)



def read_txt_to_json(txt_file, json_file):
    data = []
    with open(txt_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    for line in lines:
        if line.strip() == "":
            continue
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
    json.dump(data, open(json_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)





if __name__ == "__main__":
    # read_pdf_to_txt(f"../data/上海证券交易所债券交易规则.pdf", f"../data/上海证券交易所债券交易规则.txt")
    # read_txt_to_json(f"../data/上海证券交易所债券交易规则.txt", f"../data/上海证券交易所债券交易规则.json")
    # exit(0)
    for file in os.listdir("../data/深交所业务规则/origin"):
        if "pdf" in file:
            read_pdf_to_txt(f"../data/深交所业务规则/origin/{file}", f"../data/深交所业务规则/txt/{file[:-4]}.txt")
            read_txt_to_json(f"../data/深交所业务规则/txt/{file[:-4]}.txt", f"../data/深交所业务规则/json_for_sequence_classification/{file[:-4]}.json")
        else:  # "docx"
            ...

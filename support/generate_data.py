import pdfplumber
import json
import os


# 读取pdf，将其写入一个txt文件中
def read_pdf_to_txt(pdf_file, txt_file):
    s = ""
    with pdfplumber.open(pdf_file) as pdf:
        for page in pdf.pages:
            s += f"{page.extract_text()}\n"
    ts = ""
    for i, line in enumerate(s.split("\n")):
        if i == 0 or i == 1 and "附件" in ts or line == "":
            ts += line + "\n"
            continue
        # 第几章，第几节
        if line[0] == "第" and " " in line and ("章" in line or "节" in line):
            ts += line + "\n"
        elif line[-1] == "。" or line[-1] == "；" or line[-1] == "：" or line[-1] == ":":
            ts += line + "\n"
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
        d = {"text":line.strip(), "label": "", "type": ""}
        data.append(d)
    json.dump(data, open(json_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)





if __name__ == "__main__":
    read_txt_to_json("../data/上海证券交易所债券交易规则.txt", "上海证券交易所债券交易规则.json")
    # for file in os.listdir("../data/深交所业务规则/origin"):
    #     if "pdf" in file:
    #         read_pdf_to_txt(f"../data/深交所业务规则/origin/{file}", f"../data/深交所业务规则/txt/{file[:-4]}.txt")
    #         read_txt_to_json(f"../data/深交所业务规则/txt/{file[:-4]}.txt", f"../data/深交所业务规则/json/{file[:-4]}.json")
    #     else:  # "docx"
    #         ...
    #     # read_txt_to_json(f"../data/深交所业务规则/txt/{file[:-4]}.txt", f"../data/深交所业务规则/json/{file[:-4]}.json")

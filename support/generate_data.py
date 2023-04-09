import pdfplumber
import json
import os


def is_id(str):
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
    last_line = ""
    for i, line in enumerate(s.split("\n")):
        if i == 0 or i == 1 and "附件" in ts or line == "":  # 附件名、标题、空行
            ts += line + "\n"
            last_line = line
            continue
        # 第几章，第几节
        if line[0] == "第" and " " in line and ("章" in line or "节" in line):
            ts += "\n" + line + "\n"
        elif is_id(line) and last_line.strip()[-1] == "。":  # 遇到1.1.1这样的
            ts += "\n" + line
        elif line[0] == "—" and line[-1] == "—":
            continue
        else:
            ts += line
        last_line = line

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
            d = {"text": text.strip(), "label": "", "type": "", "id": id}
        else:
            d = {"text": line.strip(), "label": "", "type": ""}
        data.append(d)
    json.dump(data, open(json_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)





if __name__ == "__main__":
    for file in os.listdir("../data/深交所业务规则/origin"):
        if "pdf" in file:
            read_pdf_to_txt(f"../data/深交所业务规则/origin/{file}", f"../data/深交所业务规则/txt/{file[:-4]}.txt")
            read_txt_to_json(f"../data/深交所业务规则/txt/{file[:-4]}.txt", f"../data/深交所业务规则/json/{file[:-4]}.json")
        else:  # "docx"
            ...
        # read_txt_to_json(f"../data/深交所业务规则/txt/{file[:-4]}.txt", f"../data/深交所业务规则/json/{file[:-4]}.json")

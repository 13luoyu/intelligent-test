from support.generate_data_for_sequence_classification import read_pdf_to_txt, read_txt_to_json
import json

def nl_to_sci(nl_file = None, nl_data = None):
    '''
    将自然语言文档（pdf格式）或自然语言输入转化为sequence classification input的格式
    nl_file: pdf格式的自然语言文档
    nl_data: 数组，每个数组元素为一条规则
    sci: 返回转化好的sequence classification input数据
    '''
    if nl_file is not None and len(nl_file) >= 5 and nl_file[-4:] == ".pdf":
        # filename = nl_file.split('/')[-1].split('.')[0]
        txt_data = read_pdf_to_txt(nl_file)
        sci = read_txt_to_json(txt_data)
    elif nl_data is not None:
        sci = read_txt_to_json(nl_data)
    else:
        raise ValueError("未指定输入文件或输入文字")
    return sci


if __name__ == "__main__":
    input_data = open("rules_cache/input.txt", "r", encoding="utf-8").readlines()
    sci = nl_to_sci(nl_data = input_data)
    json.dump(sci, open("rules_cache/sci.json", "r", encoding="utf-8"), ensure_ascii=False, indent=4)
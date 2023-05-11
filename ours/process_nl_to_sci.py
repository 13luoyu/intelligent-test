# 将自然语言文档（pdf格式）转化为sequence classification input格式

from support.generate_data_for_sequence_classification import read_pdf_to_txt, read_txt_to_json

def nl_to_sci(nl_file, sci_file):
    if nl_file[-4:] == ".pdf":
        read_pdf_to_txt(nl_file, f"rules_cache/{nl_file[:-4]}.txt")
        read_txt_to_json(f"rules_cache/{nl_file[:-4]}.txt", sci_file)
    elif nl_file[-4:] == ".txt":
        read_txt_to_json(nl_file, sci_file)


if __name__ == "__main__":
    nl_to_sci("rules_cache/input.txt", "rules_cache/sci.json")
from support.generate_data_for_sequence_classification import read_pdf_to_txt, read_txt_to_json
import json

def get_market_variety(s, knowledge):
    market, market_num, variety, variety_num = "", 0, "", 0
    for key in knowledge:
        if key == "交易市场":
            values = knowledge[key]
            for value in values:
                value_count = s.count(value)
                if value_count > market_num:
                    market_num = value_count
                    market = value
        elif key == "交易品种":
            values = knowledge[key]
            for value in values:
                value_count = s.split("\n")[0].count(value)
                if value_count > variety_num:
                    variety_num = value_count
                    variety = value
    
    if market_num == 0:
        if "\n".join(s.split("\n")).count("深圳") > "\n".join(s.split("\n")).count("上海"):
            market = "深圳证券交易所"
        elif "\n".join(s.split("\n")).count("深圳") < "\n".join(s.split("\n")).count("上海"):
            market = "上海证券交易所"
        else:
            if "\n".join(s.split("\n")).count("深交所") > "\n".join(s.split("\n")).count("上交所"):
                market = "深圳证券交易所"
            elif "\n".join(s.split("\n")).count("深交所") < "\n".join(s.split("\n")).count("上交所"):
                market = "上海证券交易所"
            else:
                market = "证券交易所"
    if variety_num == 0:
        variety = "证券"
    return {"market": market, "variety": variety}


def nl_to_sci(nl_file = None, nl_data = None, knowledge = "../data/knowledge.json"):
    '''
    将自然语言文档（pdf格式）或自然语言输入转化为sequence classification input的格式
    nl_file: pdf格式的自然语言文档
    nl_data: 数组，每个数组元素为一条规则
    sci: 返回转化好的sequence classification input数据
    '''
    know = json.load(open(knowledge, "r", encoding="utf-8"))
    if nl_file is not None and len(nl_file) >= 5 and nl_file[-4:] == ".pdf":
        # filename = nl_file.split('/')[-1].split('.')[0]
        txt_data = read_pdf_to_txt(nl_file)
        sci = read_txt_to_json(txt_data)
        market_variety = get_market_variety(txt_data, know)
    elif nl_data is not None:
        sci = read_txt_to_json(nl_data)
        market_variety = get_market_variety(nl_data, know)
    else:
        raise ValueError("未指定输入文件或输入文字")

    return sci, market_variety


if __name__ == "__main__":
    sci, market_variety = nl_to_sci(nl_file="rules_cache/深圳证券交易所债券交易规则.pdf")
    # input_data = open("rules_cache/input.txt", "r", encoding="utf-8").readlines()
    # sci, market_variety = nl_to_sci(nl_data = input_data)
    json.dump(sci, open("rules_cache/sci.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(market_variety, open("rules_cache/setting.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
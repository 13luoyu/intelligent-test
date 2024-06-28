from support.generate_data_for_sequence_classification import read_pdf_to_txt, read_txt_to_json, is_id
import json
import os
from transfer.knowledge_tree import encode_tree

def get_market_variety(s, knowledge):
    market, market_num, variety, variety_num = "", 0, "", 0
    tree = encode_tree(knowledge)

    markets, varieties = [], []
    # 所有的品种/业务有：
    # variety = ["债券","可转债","股票","创业板","基金","基础设施基金","权证","存托凭证","股票质押式回购交易","融资融券交易","资产管理计划份额转让","资产证券化","深港通","质押式报价回购交易"]
    for key in tree:
        if "交易市场" == key['content'].split(":")[0]:
            markets.append(key['content'].split(":")[-1])
            
        elif "品种" in key['content'].split(":")[0] or "业务" == key['content'].split(":")[0]:
            varieties.append(key['content'].split(":")[-1])

    markets = list(set(markets))
    varieties = list(set(varieties))

    market, variety = "", ""
    for value in markets:
        value_count = s.count(value)
        if value_count > market_num:
            market_num = value_count
            market = value
    s = s.strip()
    for value in varieties:
        # 统计时首先去掉开头两行，避免误导
        paper = s.split("\n")
        i = 0
        while i < len(paper) and not is_id(paper[i]):
            i += 1
        if i == 0 or i == len(paper):
            i = 2
        paper = "\n".join(paper[:i])
        value_count = paper.count(value)
        if value_count >= 1 and len(value) > len(variety):
            variety = value
            variety_num = value_count

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


def nl_to_sci(nl_file = None, nl_data = None, knowledge=None):
    '''
    将自然语言文档（pdf格式）或自然语言输入转化为sequence classification input的格式
    nl_file: pdf格式的自然语言文档
    nl_data: 数组,每个数组元素为一条规则
    sci: 返回转化好的sequence classification input数据
    '''
    if nl_file is not None and len(nl_file) >= 5 and nl_file[-4:] == ".pdf":
        # filename = nl_file.split('/')[-1].split('.')[0]
        txt_data = read_pdf_to_txt(nl_file)
        sci = read_txt_to_json(txt_data)
        market_variety = get_market_variety(txt_data, knowledge)
    elif nl_data is not None:
        sci = read_txt_to_json(nl_data)
        market_variety = get_market_variety(nl_data, knowledge)
    else:
        return [], {}

    return sci, market_variety


if __name__ == "__main__":
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json", "r", encoding="utf-8"))
    for file in os.listdir("../data/business_rules/origin/"):
        filepath = "../data/business_rules/origin/" + file
        sci, market_variety = nl_to_sci(nl_file=filepath, nl_data=None, knowledge=knowledge)
        print(file, market_variety)
    
    sci, market_variety = nl_to_sci(nl_file="cache/深圳证券交易所债券交易规则.pdf", knowledge=knowledge)
    # input_data = open("cache/input.txt", "r", encoding="utf-8").readlines()
    # sci, market_variety = nl_to_sci(nl_data = input_data)
    json.dump(sci, open("cache/sci.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(market_variety, open("cache/setting.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
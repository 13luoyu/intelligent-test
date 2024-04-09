from ours.process_nl_to_sci import nl_to_sci
import json
import os


if __name__ == "__main__":
    knowledge = json.load(open("../data/domain_knowledge/classification_knowledge.json", "r", encoding="utf-8"))
    for file in os.listdir("../data/data_for_LLM_v1/business_rules/origin/"):
        filepath = "../data/data_for_LLM_v1/business_rules/origin/" + file
        sci, market_variety = nl_to_sci(nl_file = filepath, nl_data = None, knowledge=knowledge)
        print(file, market_variety)

    sci, market_variety = nl_to_sci(nl_file="cache/深圳证券交易所债券交易规则.pdf", knowledge=knowledge)
    # input_data = open("cache/input.txt", "r", encoding="utf-8").readlines()
    # sci, market_variety = nl_to_sci(nl_data = input_data)
    
    json.dump(sci, open("cache/sci.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    json.dump(market_variety, open("cache/setting.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
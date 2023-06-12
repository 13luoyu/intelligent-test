import os
import json

def integrate(in_dir: str, out_file: str):
    all_file = []
    for file in os.listdir(in_dir):
        if "finish" in file:
            rules = json.load(open(in_dir + file, "r", encoding="utf-8"))
            all_file += rules
    json.dump(all_file, open(out_file, "w", encoding="utf-8"), ensure_ascii=False, indent=4)


if __name__ == "__main__":
    integrate("../data/业务规则/json_for_sequence_classification/", "../data/sc_data.json")
    integrate("../data/业务规则/json_for_token_classification/", "../data/tc_data.json")
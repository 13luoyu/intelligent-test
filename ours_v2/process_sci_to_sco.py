from ours.process_sci_to_sco import sequence_classification
import json


if __name__ == "__main__":
    sci_data = json.load(open("cache/sci.json", "r", encoding="utf-8"))
    sco_data = sequence_classification(sci_data, "../model/trained/mengzi_rule_filtering")
    json.dump(sco_data, open("cache/sco.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)



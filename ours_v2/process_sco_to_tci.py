from ours.process_sco_to_tci import sco_to_tci
import json

if __name__ == "__main__":
    sco_data = json.load(open("cache/sco.json", "r", encoding="utf-8"))
    tci_data = sco_to_tci(sco_data)
    json.dump(tci_data, open("cache/tci.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)
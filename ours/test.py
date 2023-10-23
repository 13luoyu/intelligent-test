from transfer import mydsl_to_rules
import pprint
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2
import json


if __name__ == "__main__":
    s = open("rules_cache/r1.mydsl", "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(s)
    rules, vars = preprocess(rules, vars)
    # pprint.pprint(rules)
    preliminaries = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, preliminaries)
    pprint.pprint(rules)
from transfer import mydsl_to_rules
import pprint
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2
from ours.process_r2_to_r3 import compose_rules_r2_r3
import json

def test_r1_r2():
    s = open("rules_cache/r1.mydsl", "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(s)
    rules, vars = preprocess(rules, vars)
    # pprint.pprint(rules)
    preliminaries = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, preliminaries)
    pprint.pprint(rules)

def test_r2_r3():
    s = open("rules_cache/r2.mydsl", "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(s)
    preliminaries = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, preliminaries)
    pprint.pprint(rules)

if __name__ == "__main__":
    # test_r1_r2()
    test_r2_r3()
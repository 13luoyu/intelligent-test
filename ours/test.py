from ours.process_testcase_to_outputs import generate_dicts
from transfer import mydsl_to_rules
import pprint
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2, construct_tree
from ours.process_r2_to_r3 import compose_rules_r2_r3
from ours.process_r3_to_testcase import testcase
import json
from hashlib import md5
import time
import wget
import os

def test_r1_r2():
    s = open("rules_cache/r1.mydsl", "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(s)
    rules, vars = preprocess(rules, vars)
    preliminaries = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, preliminaries)
    pprint.pprint(rules, open("a.txt", "w", encoding="utf-8"))

def test_r2_r3():
    s = open("rules_cache/r2.mydsl", "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(s)
    preliminaries = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, preliminaries)
    pprint.pprint(rules)

def test_r3_testcase():
    s = open("rules_cache/r3.mydsl", "r", encoding="utf-8").read()
    defines, vars, rules = mydsl_to_rules.mydsl_to_rules(s)
    vars = testcase(defines, vars, rules)
    outputs = generate_dicts(vars, rules)
    out_num = 0
    for o in outputs:
        out_num += len(o)
    print(f"testcase生成，数目为：{out_num}")
    json.dump(outputs, open("a.json", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

app_secret_key = "aitest"
def get_timestamp_sign():
    timestamp = str(int(time.time() * 1000))
    sign = md5(f"{timestamp}{app_secret_key}".encode("utf-8")).hexdigest().upper()
    return timestamp, sign

if __name__ == "__main__":
    # test_r1_r2()
    # test_r2_r3()
    # test_r3_testcase()
    print(get_timestamp_sign())
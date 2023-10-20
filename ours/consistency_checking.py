import json
import pprint
from transfer.mydsl_to_rules import mydsl_to_rules

def consistency_checking(data, source):
    defines, vars, rules = mydsl_to_rules(data)
    conflict_rules = []  # {ids: [id1, id2], reason: ''}
    rule_ids = list(rules.keys())
    for i, id1 in enumerate(rule_ids):
        for j, id2 in enumerate(rule_ids):
            if j <= i:
                continue
            rule1, rule2 = rules[id1], rules[id2]
            cons1, cons2, res1, res2 = sorted(rule1['constraints'], key=lambda x:x['key']), sorted(rule2['constraints'], key=lambda x:x['key']), sorted(rule1['results'], key=lambda x:x['key']), sorted(rule2['results'], key=lambda x:x['key'])
            
            then_same = True
            for i, r1 in enumerate(res1):
                for r2 in res2:
                    if r1 != r2:
                        then_same = False
                        break
                if not then_same:
                    break
            
            if_same = True
            for c1 in cons1:
                for c2 in cons2:
                    if c1 != c2:
                        if_same = False
                        break
                if not if_same:
                    break



if __name__ == "__main__":
    input_data = json.load(open("rules_cache/consistency_checking_input.json", "r", encoding="utf-8"))
    consistency_checking(input_data['data'], input_data['source'])





# then相同、then不同
# key相同（value同，value不同）、key包含、key有交集、key没有交集
# 通用标签、特殊标签
# 不冲突、不冲突


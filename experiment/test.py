import json
from experiment.compare_BR import str_same

with open("data/exp1_3_claude2.txt", "r", encoding="utf-8") as f:
    lines = f.readlines()

id_from = json.load(open("data/exp1_2_input.json", "r", encoding="utf-8"))
output = open("data/exp1_3_claude3.txt", "w", encoding="utf-8")

rule_cache = []
br_cache = []
beg = False
br = ""
for line in lines:
    line = line.strip()
    if len(rule_cache) < 10:
        for i in range(1, 11):
            if line.find(f"{i}.") == 0:
                if i < 10:
                    rule_cache.append(line[2:])
                else:
                    rule_cache.append(line[3:])
    elif "```" in line and not beg:
        beg = True
    elif "```" in line and beg:
        beg = False
        for i in range(min(len(rule_cache), len(br_cache))):
            for idf in id_from:
                if str_same(idf["text"], rule_cache[i], 0.8):
                    output.write(f"rule {idf['id']}\n{br_cache[i]}\n")
                    output.flush()
                    break
        br = ""
        rule_cache = []
        br_cache = []
    
    if beg and "if" in line:
        br = line
    elif beg and "then" in line:
        br += "\n" + line + "\n"
        br_cache.append(br)

output.close()
# 给一个存储R规则的文件，打印它的constraint数目

def count(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    constraint_num = 0
    for line in lines:
        if "if" in line or "then" in line:
            and_num = line.count("and")
            constraint_num += and_num + 1
    print(constraint_num)



count("../ours/rules_cache/r1.mydsl")
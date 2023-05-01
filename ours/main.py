# 主程序
from process_r1_to_r2 import preprocess, compose_rules_r1_r2
from process_r2_to_r3 import compose_rules_r2_r3
from process_r3_to_testcase import testcase
from process_testcase_to_outputs import generate_dicts
from transfer import mydsl_to_rules
import json

def main():
    # 读文件
    defines, vars, rules = mydsl_to_rules.read_file("r1.mydsl")
    # 领域知识
    knowledge = json.load(open("../data/knowledge.json", "r", encoding="utf-8"))
    # 文件预处理，将rules中某些自然语言描述的规则转换为数学表达式
    rules = preprocess(rules)
    json.dump(rules, open("rules_cache/r1.txt", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # R1->R2
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
    json.dump(rules, open("rules_cache/r2.txt", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # R2->R3
    defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
    json.dump(rules, open("rules_cache/r3.txt", "w", encoding="utf-8"), ensure_ascii=False, indent=4)

    # 生成测试样例
    vars = testcase(defines, vars, rules)
    outputs = generate_dicts(vars, rules)

    # 保存结果
    out_num = 0
    for o in outputs:
        out_num += len(o)
    print(f"testcase包含的规则数：{out_num}")
    json.dump(rules, open("rules_cache/textcase.txt", "w", encoding="utf-8"), ensure_ascii=False, indent=4)



if __name__ == "__main__":
    main()
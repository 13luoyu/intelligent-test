# 生成测试用例
import os
import json
from experiment.compare_BR import compute_BR_num, compute_BR_precision
from transfer import mydsl_to_rules
from ours.process_r3_to_testcase import testcase
from ours.process_testcase_to_outputs import generate_dicts

if __name__ == "__main__":
    fp = open("data/exp3_result.log", "w", encoding="utf-8")

    print("我们的结果：")
    fp.write("我们的结果：\n")
    
    for file in sorted(os.listdir("data/")):
        if "exp2_input" in file and "r3" in file:
            defines, vars, rules = mydsl_to_rules.read_file(f"data/{file}")
            # 生成测试用例
            vars = testcase(defines, vars, rules)
            outputs = generate_dicts(vars, rules)
            out_num = 0
            for o in outputs:
                out_num += len(o)
            print(f"数据集{file[10]}，规则数{out_num}")
            json.dump(outputs, open(f"data/exp3_output{file[10]}.txt", "w", encoding="utf-8"), ensure_ascii=False, indent=4)


    fp.close()
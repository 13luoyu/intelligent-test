from ours import main
import time
import os

if __name__ == "__main__":
    output = open("rules_cache/time_consume.log", "w", encoding="utf-8")
    for i, file in enumerate(sorted(os.listdir("rules_cache"))):
        if "input" in file and "all" not in file:
            begin_time = time.time()
            main.nlp_process(f"rules_cache/{file}", "rules_cache/sci.json", "rules_cache/sco.json", "rules_cache/tci.json", "rules_cache/tco.json", "rules_cache/r1.mydsl", "../data/knowledge.json", "../model/ours/best_1690658708", "../model/ours/best_1690329462", "../data/tc_data.dict")
            r3_time = main.alg_process("rules_cache/r1.mydsl", "rules_cache/r1.json", "rules_cache/r2.json", "rules_cache/r3.json", "rules_cache/testcase.json", "../data/knowledge.json")
            
            r3_consume = round(r3_time - begin_time, 3)
            time_consume = round(time.time() - begin_time, 3)
            print(f"数据集{file}, 规则生成用时: {r3_consume}, 总共消耗时间: {time_consume}")
            output.write(f"数据集{file}, 规则生成用时: {r3_consume}, 总共消耗时间: {time_consume}\n")
    output.close()
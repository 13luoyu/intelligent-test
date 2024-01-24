from ours.main import nlp_process, alg_process
import time
import os

def generate_rules_testcases_all():
    for file in os.listdir("data/"):
        if ".pdf" in file:
            # if "深圳证券交易所交易规则" not in file:
            #     continue
            filename = file[:-4]
            print(f"文件《{filename}》开始执行")
            begin_time = time.time()
            nlp_process("data/" + file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/knowledge.json", "../data/terms.txt", "../model/ours/best_1690658708", "../model/ours/best_1701809213", "../data/tc_data.dict")
            alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"rules_and_testcases/{filename}_rules.mydsl", f"rules_and_testcases/{filename}_testcases.json", "../data/knowledge.json", "cache/relation.json", "cache/explicit_relation.json", "cache/implicit_relation.json")
            time_consume = time.time() - begin_time
            print(f"《{filename}》总共消耗时间: {time_consume}")



if __name__ == "__main__":
    generate_rules_testcases_all()
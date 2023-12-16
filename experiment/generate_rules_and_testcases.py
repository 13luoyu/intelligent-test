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
            nlp_process("data/" + file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/knowledge.json", "../model/ours/best_1690658708", "../model/ours/best_1696264421", "../data/tc_data.dict")
            alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"rules_and_testcases/{filename}_rules.mydsl", f"rules_and_testcases/{filename}_testcases.json", "../data/knowledge.json")
            time_consume = time.time() - begin_time
            print(f"《{filename}》总共消耗时间: {time_consume}")


def add_trading_method(file, trading_method):
    data = open(file, "r", encoding="utf-8").read()
    data = f"define 交易方式 = {trading_method}\n{data}"
    with open(file, "w", encoding="utf-8") as f:
        f.write(data)


def generate_rules_testcases_part():
    for file in os.listdir("data/"):
        if ".txt" in file:
            # if "data2" not in file:
            #     continue
            filename = file[:-4]
            begin_time = time.time()
            nlp_process("data/" + file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/knowledge.json", "../model/ours/best_1690658708", "../model/ours/best_1701809213", "../data/tc_data.dict")
            first_line = open("data/"+file, "r", encoding="utf-8").readlines()[0].strip()
            if "盘后定价交易" in first_line:
                add_trading_method("cache/r1.mydsl", "盘后定价交易")
            elif "大宗交易" in first_line:
                add_trading_method("cache/r1.mydsl", "大宗交易")
            elif "竞价交易" in first_line:
                add_trading_method("cache/r1.mydsl", "竞价交易")
            alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", "cache/r2.mydsl", "cache/r3.json", f"rules_and_testcases_part/{filename}_rules.mydsl", f"rules_and_testcases_part/{filename}_testcases.json", "../data/knowledge.json")
            time_consume = time.time() - begin_time
            print(f"《{filename}》总共消耗时间: {time_consume}")



if __name__ == "__main__":
    # generate_rules_testcases_all()
    generate_rules_testcases_part()
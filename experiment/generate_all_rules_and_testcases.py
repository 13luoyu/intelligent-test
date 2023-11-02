from ours.main import nlp_process, alg_process
import time
import os

if __name__ == "__main__":
    for file in os.listdir("data/"):
        if ".pdf" in file:
            # if "约定购回式证券交易及登记结算业务办法" in file or "深圳证券交易所深港通业务实施办法" in file or "境外证券交易所互联互通" in file or "深圳证券交易所公开募集基础设施证券" in file:
            #     continue
            filename = file[:-4]
            begin_time = time.time()
            nlp_process("data/" + file, "cache/setting.json", "cache/sci.json", "cache/sco.json", "cache/tci.json", "cache/tco.json", "cache/r1.mydsl", "../data/knowledge.json", "../model/ours/best_1690658708", "../model/ours/best_1696264421", "../data/tc_data.dict")
            alg_process("cache/r1.mydsl", "cache/r1.json", "cache/r2.json", f"rules_and_testcases/{filename}_rules.json", f"rules_and_testcases/{filename}_testcases.json", "../data/knowledge.json")
            time_consume = time.time() - begin_time
            print(f"《{filename}》总共消耗时间: {time_consume}")
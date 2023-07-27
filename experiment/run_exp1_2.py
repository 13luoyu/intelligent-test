from experiment.exp1_2 import *
import json
import os

# nohup python run_exp1_2.py >data/exp1_2.log &

if __name__ == "__main__":
    for d in os.listdir("../model/ours"):
        if "best" in d:
            token_classification("data/exp1_2_input.json", "data/exp1_2_output.json", "../data/knowledge.json", "../model/ours/" + d, "../data/tc_data.dict")
            # 整合预测与真实值
            integrate_tc("../data/rules.json", "data/exp1_2_output.json", "data/exp1_2_compare.log")
            # 评估
            evaluate("data/exp1_2_compare.log", "data/exp1_2_result.log", threshold=0.6)
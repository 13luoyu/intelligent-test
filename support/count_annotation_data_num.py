import os
import json


def count_annotate_num():
    print("规则过滤任务")
    sc_data = json.load(open("../data/data_for_LLM_encoder/sc_data.json", "r", encoding="utf-8"))
    sc_rule, sc_know, sc_non_rule = 0, 0, 0
    for data in sc_data:
        if data['type'] == "0":
            sc_non_rule += 1
        elif data['type'] == "1":
            sc_rule += 1
        elif data['type'] == "2":
            sc_know += 1
    print(f"总共标注了 {len(sc_data)} 条数据，其中包含可测试的规则 {sc_rule} 条，领域知识 {sc_know} 条，无需测试的规则 {sc_non_rule} 条")


    print("规则元素抽取任务")
    tc_data = json.load(open("../data/data_for_LLM_encoder/tc_data.json", "r", encoding="utf-8"))
    print(f"总共标注了 {len(tc_data)} 条数据")


def count_know_num():
    knows = json.load(open("../data/domain_knowledge/knowledge.json", "r", encoding="utf-8"))
    is_a, has_a = 0, 0
    for key in list(knows.keys()):
        if key in ["authority", "stateMachine"]:
            continue
        value = knows[key]
        if isinstance(value, list):
            has_a += 1
        elif isinstance(value, str):
            is_a += 1
    print(f"知识库总共包含 {is_a + has_a} 条知识，其中解释型知识 {is_a} 条，分类型知识 {has_a} 条")



if __name__ == "__main__":
    count_annotate_num()
    count_know_num()
import json
from openpyxl import Workbook
import os

def to_excel(data, output_file):
    workbook = Workbook()
    sheet = workbook.active

    # 获取所有key
    all_key = []
    for d in data:
        all_key += list(d.keys())
    all_key = list(set(all_key))
    # 所有key排序输出
    new_all_key = []
    key_order = ["rule", "testid", "测试关注点", "交易市场", "交易品种", "交易方式", "交易方向", "操作", "时间", "数量", "价格"]
    for key in key_order:
        for ki in all_key:
            if key in ki and ki not in new_all_key:
                new_all_key.append(ki)
    result_key = []
    for key in all_key:
        if "结果" not in key and key not in new_all_key:
            new_all_key.append(key)
        if "结果" in key:
            result_key.append(key)
    for key in sorted(result_key,reverse=True):
        new_all_key.append(key)
    all_key = new_all_key
    sheet.append(all_key)

    for d in data:
        values = []
        for key in all_key:
            if key in d:
                values.append(str(d[key]))
            else:
                values.append("")
        sheet.append(values)
    workbook.save(output_file)


def llm_to_excel():
    for file in os.listdir("llm_result"):
        if "chatgpt" in file and "json" in file:
            print(f"处理文件{file}")
            data = json.load(open(f"llm_result/{file}", "r", encoding="utf-8"))
            to_excel(data, f"excel/chatgpt_{file.split('_')[-1].split('.')[0]}.xlsx")

def ours_to_excel():
    for file in os.listdir("rules_and_testcases_part"):
        if "testcases" in file:
            print(f"处理文件{file}")
            data = json.load(open(f"rules_and_testcases_part/{file}", "r", encoding="utf-8"))
            data = [di for d in data for di in d]
            to_excel(data, f"excel/ours_{file.split('_')[0]}.xlsx")

def non_expert_to_excel():
    for file in os.listdir("non_expert_result"):
        if "ly" in file and ".json" in file:
            print(f"处理文件{file}")
            data = json.load(open(f"non_expert_result/{file}", "r", encoding="utf-8"))
            to_excel(data, f"excel/non_expert_{file.split('_')[-1].split('.')[0]}.xlsx")

if __name__ == "__main__":
    llm_to_excel()
    ours_to_excel()
    non_expert_to_excel()
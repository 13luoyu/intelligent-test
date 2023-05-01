import re
import json


# 读文件
def read_file(file_name):
    """读文件并解析, 将常量写入defines, 变量写入vars, 规则写入rules"""

    defines = dict()
# defines = {"交易结果": ['已申报', '未申报'], }
    vars = dict()
# vars = {
#   '4.1.1': {'中标方式': [1, 2], '交易方式': [1, 2], '操作': [1, 2]},
# }
    rules = dict()
# rules = {
#   '4.1.1.1': {'constraints': [{'key': '交易方式', 'operation': 'is', 'value': '竞买成交'},
#                            {'key': '操作', 'operation': 'is', 'value': '竞买预约申报'},
#                            {'key': '中标方式',
#                             'operation': 'is',
#                             'value': '单一主体中标'}],
#            'results': [{'else': '未申报', 'key': '交易结果', 'value': '已申报'}], 
#            'focus': ['订单连续性操作'],
#            'rule_class': '4.1.1'},
# }

    with open(file_name, "r", encoding="utf-8") as f:
        lines = f.readlines()
    for line in lines:
        l = line.strip().split()
        
        # 跳过空行
        if len(l) == 0:
            continue
        if l[0] == "rule":
            rule_class = '.'.join(l[1].split(".")[:-1])
            rule_id = l[1]
            rules[rule_id] = {}
            vars[rule_id] = {}
            rules[rule_id]["rule_class"] = [rule_class]
        
        elif l[0] == 'focus:':
            focus = l[1]
            rules[rule_id]["focus"] = [focus]

        elif l[0] == "if":
            constraints = []
            i = 1
            while i < len(l):
                constraint = dict()
                vars[rule_id][l[i]] = []
                constraint["key"] = l[i]
                constraint["value"] = l[i + 2][1:-1]
                constraints.append(constraint)
                i = i + 4
            
            rules[rule_id]["constraints"] = constraints
        
        
        elif l[0] == "then":
            i = 1
            results = []
            while i < len(l):
                result = dict()
                result["key"] = l[i]
                result["value"] = l[i + 2][1:-1]
                if "不" in result["value"]:  # 默认result["key"][0] == "不"
                    result["else"] = result["value"][1:]
                else: # then 结果 is "成功"
                    result["else"] = "不" + result["value"]
                results.append(result)
                i += 4
            rules[rule_id]["results"] = results
        



    defines['交易市场'] = ["深圳证券交易所"]
    defines['交易品种'] = ["债券"]
    return defines, vars, rules





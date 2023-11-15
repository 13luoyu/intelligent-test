
# 读文件
import json


def mydsl_to_rules(s):
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

    lines = s.split("\n")
    for line in lines:
        l = line.strip().split()
        
        # 跳过空行
        if len(l) == 0:
            continue
        if l[0] == "define":
            defines[l[1]] = [l[3]]
        if l[0] == "rule":
            # if "_" in l[1]:
            #     rule_class = l[1].split("_")[0]
            # else:
            #     rule_class = '.'.join(l[1].split(".")[:-1])
            rule_id = l[1]
            rules[rule_id] = {}
            vars[rule_id] = {}
            # rules[rule_id]["rule_class"] = [rule_class]
        
        elif l[0] == 'sourceId':
            rules[rule_id]["rule_class"] = l[1].split(',')
        
        elif l[0] == 'focus:':
            focus = l[1]
            rules[rule_id]["focus"] = focus.split(",")

        elif l[0] == "if":
            constraints = []
            i = 1
            while i < len(l):
                constraint = dict()
                
                constraint["key"] = l[i]
                if l[i] == "单笔最大申报数量" or l[i] == "单笔申报最大数量":
                    constraint["key"] = "申报数量"
                    l[i] = "申报数量"
                if l[i+1] == "is":
                    constraint["value"] = l[i + 2][1:-1]
                elif l[i+1] == "in":
                    constraint["value"] = l[i + 2]
                else:
                    constraint["value"] = l[i+1] + l[i+2][1:-1]
                
                constraint["operation"] = l[i+1]
                constraints.append(constraint)
                vars[rule_id][l[i]] = []
                i = i + 4
            
            rules[rule_id]["constraints"] = constraints
        
        
        elif l[0] == "then":
            i = 1
            results = []
            while i < len(l):
                result = dict()
                result["key"] = l[i]
                result["value"] = l[i + 2][1:-1]
                result["operation"] = "is"
                if "不" in result["value"]:  # 默认result["key"][0] == "不"
                    result["else"] = result["value"][1:]
                else: # then 结果 is "成功"
                    result["else"] = "不" + result["value"]
                results.append(result)
                i += 4
            rules[rule_id]["results"] = results
        
        elif l[0] == "constraint":
            constraints = rules[rule_id]["constraints"]
            i = 1
            next_and = i + 1
            while i < len(l):
                next_and = i + 1
                while next_and < len(l) and l[next_and] != "and":
                    next_and += 1
                constraint = dict()
                
                constraint["key"] = l[i]
                constraint["value"] = l[i + 1:next_and]
                constraint["operation"] = "compute"
                constraints.append(constraint)
                vars[rule_id][l[i]] = []
                i = next_and + 1
            
            rules[rule_id]["constraints"] = constraints

        elif l[0] == "before:":
            rules[rule_id]['before'] = json.loads(" ".join(l[1:]).replace("\'", "\""))
        elif l[0] == "after:":
            rules[rule_id]['after'] = json.loads(" ".join(l[1:]).replace("\'", "\""))

    return defines, vars, rules




if __name__ == "__main__":
    s = open("../ours/rules_cache/r3.mydsl").read()
    setting = json.load(open("../ours/rules_cache/setting.json"))
    print(mydsl_to_rules(s, setting))

import json
import collections
from pprint import pprint
import cn2an


# 每个关键字所选择的答案
# outputs = []
# 所有测试用例的list
# tests = []
# 针对所有rule的输出结果，{rule_id:xxx, tests:[xxx,xxx,...]}
# results = []
# 所有测试关注点的list
# all_testkeys = []
# # 所有测试点及其对应的值
# alldicts = []

qwq_sum = 0
testid = 1

def prase_rule(outputs, ruleid, keys,rule):
    global qwq_sum
    global testid

    retans = collections.OrderedDict()
    retans['rule'] = ruleid
    retans['测试关注点'] = rule['focus'][0]
    retans['testid'] = f"{ruleid}_{testid}"
    testid += 1
    #
    # 将判断结果接在最后面

    for i in range(len(outputs)):
        if isinstance(outputs[i][1], list):
            retans[outputs[i][0]] = (str(outputs[i][1]).replace('[', '').replace(']', '').replace('\'', '')).replace(',',' 或')
        else:
            retans[outputs[i][0]] = outputs[i][1]


    if 'results' in rule.keys():
        if qwq_sum == 0:
            retans[rule['results'][0]['key']] = rule['results'][0]['value']
        else:
            retans[rule['results'][0]['key']] = rule['results'][0]['else']
            if "结果状态" in retans and "状态" in retans:
                if rule['results'][0]['else'] == "不成功":
                    retans['结果状态'] = retans['状态']
                else:
                    del retans['结果状态']

    # pprint(retans)
    return retans

def dfs(i, ruleid,rule, vars, keys , outputs, datadict):
    global qwq_sum
    """一个dfs，用来枚举vars中的所有情况，得到tests，在generate_test中被调用"""
    if i == len(keys):

        retans = prase_rule(outputs, ruleid, keys,rule)
        datadict.append(retans)
        return

    for cnt in range(len(vars[keys[i]])):
        qwq_sum = qwq_sum + 1 if cnt != 0 else qwq_sum
        outputs.append([keys[i],vars[keys[i]][cnt]])

        dfs(i + 1, ruleid,rule, vars , keys , outputs,datadict)
        # print(vars[keys[i]][cnt])
        outputs.pop()
        qwq_sum = qwq_sum - 1 if cnt != 0 else qwq_sum


def generate_dicts(vars, rules):
    # 将vars转换为特定格式
    ans = []
    for ruleid, var in vars.items():

        keys = list(var.keys())
        global qwq_sum,testid
        qwq_sum = 0
        testid = 1
        outputs = []
        datadict = []
        dfs(0, ruleid,rules[ruleid], var , keys, outputs,datadict)

        if datadict != []:
            ans.append(datadict)

    if len(ans) > 0 and "第" in ans[0][0]['rule'] and "条" in ans[0][0]['rule']:
        for tcs in ans:
            for tc in tcs:
                tc['temp_id'] = cn2an.cn2an(tc['rule'].split(".")[0][1:-1], "normal")
        ans = sorted(ans, key=lambda x:x[0]['temp_id'])
        for tcs in ans:
            for tc in tcs:
                del tc['temp_id']
    else:
        ans = sorted(ans, key=lambda x:x[0]['rule'])
    return ans

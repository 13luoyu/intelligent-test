import pprint
import copy

# 处理一条规则分成多个R0的策略：
# 如果一个键第二，三，...次出现，那么连带之前所有的键分为多个规则
# 分为多规则后，每出现一个新的键，遍历所有规则，如果某规则没有该键，加到这个规则上，否则不变
def to_r0(log_file, r0_file):
    with open(log_file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    
    rules = []
    for line in lines:
        if line.find("id") == 0:
            id = int(line[4:-1])
        elif line.find("text") == 0:
            text = line[6:-1]
        elif line.find("ir hat") == 0:
            ir_hat = line[8:-1]
        elif line.find("ir real") == 0:
            ir_hat = line[9:-1]
            ifs = [{}]
            thens = [{}]
            constraints = [{}]
            focus = ""
            now_text = ""
            stack = []
            splited_ir_hat = ir_hat.split(" ")
            for i, tab in enumerate(splited_ir_hat):
                if tab == "O":
                    continue
                if "操作" in tab:
                    focus = "订单连续性操作"
                if "申报数量" in tab or "申报价格" in tab:  # TODO
                    # constraint
                    for c in constraints:
                        if tab[2:] not in c:
                            c[tab[2:]] = []
                    now_text += text[i]
                    if i+1 >= len(splited_ir_hat) or splited_ir_hat[i+1][2:] != tab[2:]:  # 下一个关键字不再与当前相同
                        for c in constraints:
                            c[tab[2:]].append(now_text)
                        stack.append(tab[2:])
                        now_text = ""
                    
                    if "申报数量" in tab and focus != "":
                        focus = "申报数量"
                    elif "申报价格" in tab and focus != "":
                        focus = "申报价格"
                elif "结果" in tab:
                    # then
                    for t in thens:
                        if tab[2:] not in t:
                            t[tab[2:]] = []
                    now_text += text[i]
                    if i+1 >= len(splited_ir_hat) or splited_ir_hat[i+1][2:] != tab[2:]:
                        for t in thens:
                            t[tab[2:]].append(now_text)
                        stack.append(tab[2:])
                        now_text = ""
                else:
                    # if
                    for i_i in ifs:
                        if tab[2:] not in i_i:
                            i_i[tab[2:]] = []
                    now_text += text[i]
                    if i+1 >= len(splited_ir_hat) or tab[2:] not in splited_ir_hat[i+1]:
                        for i_i in ifs:
                            if len(i_i[tab[2:]]) > 0:  # 遇到重复的键了
                                # 如果后续某个字段为空，不分裂规则
                                # 否则分裂规则
                                
                                all_have = True
                                for j_j in ifs:
                                    if tab[2:] not in list(j_j.keys()) or len(j_j[tab[2:]]) == 0:
                                        all_have = False
                                        j_j[tab[2:]].append(now_text)
                                if not all_have:  # 这个键是要填充的
                                    break
                                else:  # 这个键是所有规则都有的，因此要分裂
                                    for p, e in enumerate(stack):
                                        if e == tab[2:]:
                                            break
                                    before_keys = stack[:p]
                                    tmp = {}
                                    for k in before_keys:
                                        tmp[k] = copy.deepcopy(i_i[k])
                                    tmp[tab[2:]] = [now_text]
                                    ifs.append(tmp)
                                    thens.append(copy.deepcopy(thens[0]))
                                    constraints.append(copy.deepcopy(constraints[0]))
                                    break
                            else:
                                i_i[tab[2:]].append(now_text)
                        stack.append(tab[2:])
                        now_text = ""

                    if "交易时间" in tab and focus != "":
                        focus = "交易时间"
            rule = {"if":ifs, "then":thens, "constraint":constraints, "id":id, "focus":focus}
            rules.append(rule)
    pprint.pprint(rules)
    exit(0)

    # R0写入文件
    with open(r0_file, "w+", encoding="utf-8") as f:
        f.write(f"id: {id}\n")
        f.write(f"focus: {focus}\n")
        f.write(f"if \n")



if __name__ == "__main__":
    to_r0("../log/ours/eval_1679626720.log", "r0.mydsl")
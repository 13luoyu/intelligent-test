import os



def analyse(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
    rule_all, rule_correct, know_all, know_corrent, all_all, all_correct = 0, 0, 0, 0, 0, 0
    for line in lines:
        if "seq" not in line:
            continue
        if "hat" in line:
            hat = int(line.split(" ")[-1][:-1])
        elif "real" in line:
            real = int(line.split(" ")[-1][:-1])
            all_all += 1
            if real == 1:
                if real == hat:
                    rule_correct += 1
                    all_correct += 1
                rule_all += 1
            elif real == 2:
                if real == hat:
                    know_corrent += 1
                    all_correct += 1
                know_all += 1
            else:
                if real == hat:
                    all_correct += 1
    print(f"{file} 统计结果：\n文件：测试集数据数：{all_all}，其中预测正确数{all_correct}，正确率{round(float(all_correct)/float(all_all), 4)}。有规则{rule_all}条，预测正确{rule_correct}条，正确率{round(float(rule_correct)/float(rule_all), 4)}；领域知识{know_all}条，预测正确{know_corrent}条，正确率{round(float(know_corrent)/float(know_all), 4)}。\n")


if __name__ == "__main__":
    for file in os.listdir("../log"):
        if "sc_eval" in file:
            analyse("../log/" + file)
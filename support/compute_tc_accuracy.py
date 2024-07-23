import os

# 计算token_classification任务中模型的预测效果

def statistic(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
        id = ""
        ir_hat, ir_real = "", ""
        acc, total = 0, 0
        for line in lines[1:]:
            if "id" in line:
                id = line[4:-1]
            if "ir hat" in line:
                ir_hat = line[8:-1]
            if "ir real" in line:
                ir_real = line[9:-1]
                ir_hat_list = ir_hat.split(" ")
                ir_real_list = ir_real.split(" ")
                total += len(ir_hat_list)
                if len(ir_hat_list) != len(ir_real_list):
                    # print(len(ir_hat_list), len(ir_real_list))
                    # print(f"{file} {id} hat和real长度不同")
                    continue
                for i in range(len(ir_hat_list)):
                    if ir_hat_list[i] == ir_real_list[i]:
                        acc += 1
                    elif "O" != ir_hat_list[i] and "O" != ir_real_list[i]:
                        if ir_hat_list[i][2:] == ir_real_list[i][2:]:
                            acc += 1

        # print(acc, total)
        print(f"{file} 统计结果：\n正确率：{float(acc) / float(total)}\n")




if __name__ == "__main__":
    filelist = os.listdir("../encoder_fine_tuning/predict_data/")
    filelist.sort()
    for file in filelist:
        if "rule_element_extraction" in file:
            statistic(f"../encoder_fine_tuning/predict_data/{file}")


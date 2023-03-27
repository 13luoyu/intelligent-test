import os

def statistic(file):
    with open(file, "r", encoding="utf-8") as f:
        lines = f.readlines()
        ir_hat, ir_real = "", ""
        acc, total = 0, 0
        for line in lines[1:]:
            if "ir hat" in line:
                ir_hat = line[8:-1]
            if "ir real" in line:
                ir_real = line[9:-1]
                for s in ir_real:
                    if s == "O" or s == "B" or s == "I":
                        total += 1
                i, j = 0, 0
                n, m = len(ir_hat), len(ir_real)
                while i < n and j < m:
                    if ir_hat[i] == "O" and ir_real[j] == "O":
                        acc += 1
                        i += 1
                        j += 1
                        continue
                    elif ir_hat[i] == "B" and ir_real[j] == "B" or ir_hat[i] == "I" and ir_real[j] == "I":
                        next_i, next_j = i+1, j+1
                        while(next_i < n and ir_hat[next_i] != "O" and ir_hat[next_i] != "I" and ir_hat[next_i] != "B"):
                            next_i += 1
                        while(next_j < m and ir_real[next_j] != "O" and ir_real[next_j] != "I" and ir_real[next_j] != "B"):
                            next_j += 1
                        if ir_hat[i:next_i] == ir_real[j:next_j]:
                            acc += 1
                        i = next_i
                        j = next_j
                        continue
                    
                    if ir_hat[i] == "O":
                        i += 1
                    elif ir_hat[i] == "I" or ir_hat[i] == "B":
                        next_i = i+1
                        while(next_i < n and ir_hat[next_i] != "O" and ir_hat[next_i] != "I" and ir_hat[next_i] != "B"):
                            next_i += 1
                        i += next_i
                    
                    if ir_real[j] == "O":
                        j += 1
                    elif ir_real[j] == "I" or ir_real[j] == "B":
                        next_j = j+1
                        while(next_j < m and ir_real[next_j] != "O" and ir_real[next_j] != "I" and ir_real[next_j] != "B"):
                            next_j += 1
                        j = next_j
        print(f"{file} acc: {float(acc) / float(total)}")




if __name__ == "__main__":
    # filelist = os.listdir("../log/mengzi/")
    # filelist.sort()
    # for file in filelist:
    #     if file == "run_ir.log":
    #         continue
    #     statistic(f"../log/mengzi/{file}")

    # filelist = os.listdir("../log/finbert/")
    # filelist.sort()
    # for file in filelist:
    #     if file == "run_ir.log":
    #         continue
    #     statistic(f"../log/finbert/{file}")

    filelist = os.listdir("../log/ours/")
    filelist.sort()
    for file in filelist:
        if file == "run.log":
            continue
        statistic(f"../log/ours/{file}")



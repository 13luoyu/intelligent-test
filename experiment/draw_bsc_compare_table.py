
if __name__ == "__main__":
    bsc_csv = "Datasets,Experts,,,,Non-Experts,,,,ChatGPT,,,,ChatGLM,,,,LLM4Fin,,\n,#TC,BSC(%),Impr.(%),Time,#TC,BSC(%),Impr.(%),Time,#TC,BSC(%),Impr.(%),Time,#TC,BSC(%),Impr.(%),Time,#TC,BSC(%),Time\n"

    bsc_rs = open("log/bsc.log", "r", encoding="utf-8").read().split("\n")
    bsc = []
    for i in range(1,6):
        b = []
        for line in bsc_rs:
            if "finbert" in line or "llama2" in line:
                continue
            if f"data{i}" in line:
                b.append(round(float(f"0.{line.split('.')[-1]}") * 100, 2))
        b = b[:1] + b[5:]
        bsc.append(b)
    
    tc_rs = open("log/testcase_num.log", "r", encoding="utf-8").read().split("\n")
    testcase_num = []
    for i in range(1,6):
        t = []
        for line in tc_rs:
            if "finbert" in line or "llama2" in line:
                continue
            if f"data{i}" in line:
                t.append(int(line.split(":")[-1].strip()))
        t = t[:1] + [round(sum(t[1:5])/4)] + t[5:]
        testcase_num.append(t)
    
    impr = []
    for i in range(0,5):
        im = []
        b = bsc[i]
        for bi in b[:-1]:
            im.append(str(round((float(b[-1]) - float(bi))/float(bi)*100, 1)))
        impr.append(im)
    
    time = []
    time_rs = open("log/time.log", "r", encoding="utf-8").read().split("\n")
    time.append(["33m","105m","30m","20m",f"{round(float(time_rs[0].split(':')[-1].strip()),2)}s"])
    time.append(["38m","90m","25m","9m",f"{round(float(time_rs[1].split(':')[-1].strip()),2)}s"])
    time.append(["30m","110m","17m","20m",f"{round(float(time_rs[2].split(':')[-1].strip()),2)}s"])
    time.append(["35m","80m","10m","30m",f"{round(float(time_rs[3].split(':')[-1].strip()),2)}s"])
    time.append(["35m","110m","15m","20m",f"{round(float(time_rs[4].split(':')[-1].strip()),2)}s"])

    for i in range(0,5):
        bsc_csv += f"Dataset{i+1},{testcase_num[i][0]},{bsc[i][0]},{impr[i][0]},{time[i][0]},{testcase_num[i][1]},{bsc[i][1]},{impr[i][1]},{time[i][1]},{testcase_num[i][2]},{bsc[i][2]},{impr[i][2]},{time[i][2]},{testcase_num[i][3]},{bsc[i][3]},{impr[i][3]},{time[i][3]},{testcase_num[i][4]},{bsc[i][4]},{time[i][4]}\n"
    
    with open("results/table3.csv", "w", encoding="utf-8") as f:
        f.write(bsc_csv)
    
import matplotlib.pyplot as plt
import numpy as np

def draw_figure(file, image):
    datasets = ["1", "2", "3", "4", "5"]
    models = ["mengzi", "finbert", "llama2"]
    # acc = [86.84, 56.05, 94.76]
    mengzi_data, finbert_data, llama2_data = [], [], []
    lines = open(file, "r", encoding="utf-8").readlines()
    for line in lines:
        for dataset in datasets:
            if "data" + dataset not in line:
                continue
            for model in models:
                if model not in line:
                    continue
                bsc = float(line.split("覆盖率为")[-1]) * 100
                if model == "mengzi":
                    mengzi_data.append(bsc)
                elif model == "finbert":
                    finbert_data.append(bsc)
                else:
                    llama2_data.append(bsc)
    
    x = np.arange(len(datasets))
    bar_width = 0.2
    plt.figure(figsize=(8,5))
    # plt.bar(x, finbert_data, bar_width, align='center', label='finbert', color="#87BC29")
    # plt.bar(x+bar_width, mengzi_data, bar_width, color="#F58561", align='center', label='mengzi')
    # plt.bar(x+bar_width*2, llama2_data, bar_width, align='center', label='llama2', color='#00A5D9')
    plt.bar(x, finbert_data, bar_width, align='center', label='FinBert', hatch="//", color="#7BC0F7", edgecolor="black", linewidth=1)
    plt.bar(x+bar_width, mengzi_data, bar_width, align='center', label='Mengzi', color="#F18226", edgecolor="black", linewidth=1)
    plt.bar(x+bar_width*2, llama2_data, bar_width, align='center', label='Llama2-7B', hatch="\\", color="#FFDB69", edgecolor="black", linewidth=1)
    for a,b in zip(x, finbert_data):
        plt.text(a, b+1, round(b, 2), ha="center", va="baseline", fontsize=12, rotation=60)
    for a,b in zip(x+bar_width, mengzi_data):
        plt.text(a+0.05, b+1, round(b, 2), ha="center", va="baseline", fontsize=12, rotation=60)
    for a,b in zip(x+bar_width*2, llama2_data):
        plt.text(a+0.08, b+1, round(b, 2), ha="center", va="baseline", fontsize=12, rotation=60)
    
    plt.xlabel("Dataset", fontsize=15)
    plt.ylabel("BSC (%)", fontsize=15)
    plt.xticks(x+bar_width, datasets, fontsize=15)
    plt.yticks([70,75,80,85,90,95,100], fontsize=15)
    plt.ylim(70, 105)
    plt.legend(fontsize=11, loc="upper right", borderaxespad=0.1)
    plt.savefig(image)



if __name__ == "__main__":
    draw_figure("log/bsc.log", "results/figure7.png")
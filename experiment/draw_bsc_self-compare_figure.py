import matplotlib.pyplot as plt
import numpy as np

def draw_figure(file, image):
    datasets = ["1", "2", "3", "4", "5"]
    models = ["mengzi", "finbert", "atom"]
    mengzi_data, finbert_data, atom_data = [], [], []
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
                    atom_data.append(bsc)
    
    x = np.arange(len(datasets))
    bar_width = 0.2
    # plt.bar(x, finbert_data, bar_width, align='center', label='finbert', color="#87BC29")
    # plt.bar(x+bar_width, mengzi_data, bar_width, color="#F58561", align='center', label='mengzi')
    # plt.bar(x+bar_width*2, atom_data, bar_width, align='center', label='atom', color='#00A5D9')
    plt.bar(x, finbert_data, bar_width, align='center', label='finbert', hatch="//", color="#87BC29", edgecolor="black", linewidth=1, alpha=0.75)
    plt.bar(x+bar_width, mengzi_data, bar_width, align='center', label='mengzi', color="#F58561", edgecolor="black", linewidth=1, alpha=0.75)
    plt.bar(x+bar_width*2, atom_data, bar_width, align='center', label='llama2', hatch="..", color="#00A5D9", edgecolor="black", linewidth=1, alpha=0.75)
    plt.xlabel("Dataset", fontsize=15)
    plt.ylabel("BSC (%)", fontsize=15)
    plt.xticks(x+bar_width, datasets, fontsize=15)
    plt.yticks(fontsize=15)
    plt.ylim(50, 100)
    plt.legend(fontsize=11.5, loc="upper right", borderaxespad=0.1)
    plt.savefig(image)



if __name__ == "__main__":
    draw_figure("log/bsc.log", "log/bsc_self-compare.png")
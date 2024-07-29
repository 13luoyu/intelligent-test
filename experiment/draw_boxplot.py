import matplotlib.pyplot as plt

expert_bsc, non_expert_bsc, chatgpt_bsc, chatglm_bsc, LLM4Fin_bsc = [83.43, 83.80, 71.15, 77.34, 60.10], [45.83, 38.58, 46.79, 42.47, 43.64], [44.61, 50.48, 61.81, 25.00, 66.35], [27.48, 45.01, 43.88, 83.02, 8.77], [96.06, 85.36, 98.18, 96.96, 82.91]
expert_time, non_expert_time, chatgpt_time, chatglm_time, LLM4Fin_time = [33, 38, 30, 35, 35], [105, 90, 110, 80, 110], [30, 25, 17, 10, 15], [20, 9, 20, 30, 20], [7.01, 6.85, 6.82, 5.57, 8.72]

plt.figure(figsize=(12, 5), dpi=120)
plt.subplot(1, 2, 1)
box1 = plt.boxplot([expert_bsc, non_expert_bsc, chatgpt_bsc, chatglm_bsc, LLM4Fin_bsc], meanline=True, patch_artist=True, boxprops=dict(facecolor=(0, 128/255, 0)), medianprops=dict(color=(0,1,1)), whiskerprops=dict(color='red'))
plt.xticks([1, 2, 3, 4, 5], ['Expert', 'Non-Expert', 'ChatGPT', 'ChatGLM', 'LLM4Fin'], fontsize=12)
plt.ylabel('Business Scenario Coverage (BSC, %)', fontsize=15)
plt.yticks(fontsize=13)
plt.grid(True)

plt.subplot(1, 2, 2)
box2 = plt.boxplot([expert_time, non_expert_time, chatgpt_time, chatglm_time, LLM4Fin_time], meanline=True, patch_artist=True, boxprops=dict(facecolor=(1, 1, 0)), medianprops=dict(color=(0,128/255,0)), whiskerprops=dict(color='red'))
plt.xticks([1, 2, 3, 4, 5], ['Expert', 'Non-Expert', 'ChatGPT', 'ChatGLM', 'LLM4Fin'], fontsize=12)
plt.ylabel('Time Cost (min except sce for LLM4Fin)', fontsize=15)
plt.yticks(fontsize=13)
plt.grid(True)

plt.savefig("results/figure6.png")
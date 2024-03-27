import os
import json
import evaluate
import nltk


def compute_acc(results):
    word_acc, pair_acc = 0, 0
    for index, result in enumerate(results):
        answer = result['answer'].replace(" ", "").replace("\n", "").split("</s>")[0]
        prediction = result['prediction'].split("Assistant:")[-1].replace(" ", "").replace("\n", "").split("</s>")[0].replace("，", ",")
        
        if len(answer) == 0:
            acc1 = 1.0
        else:
            acc1 = 1 - float(nltk.edit_distance(answer, prediction)) / float(len(answer))
        word_acc += acc1

        answers = answer.split(",")
        predictions = prediction.split(",")
        acc2 = 0
        for i in range(len(answers)):
            if answers[i] in predictions:
                acc2 += 1
        if len(answers) == 0:
            acc2 = 1.0
        else:
            acc2 = float(acc2) / float(len(answers))
        pair_acc += acc2

        # print(acc1)
        # print(acc2)
        # print(answer)
        # print(prediction)
        # if index >= 10:
        #     exit(0)
    
    return round(word_acc / float(len(results)), 3), round(pair_acc / float(len(results)), 3)






if __name__ == "__main__":
    for file in os.listdir("../decoder_lora/predict_data/"):
        if "predict_result" in file and ".txt" not in file:
            # if "predict_result_runtime.json" not in file:
            #     continue
            results = json.load(open("../decoder_lora/predict_data/" + file, "r", encoding="utf-8"))
            acc = compute_acc(results)
            print(f"测试结果文件 {file} 的精确度为 {acc}")
            

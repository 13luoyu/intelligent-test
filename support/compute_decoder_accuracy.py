import os
import json
import evaluate
import nltk


def compute_acc(results):
    """
    results: list of dict, each dict contains 'answer' and 'prediction' key.
    :params: 'answer': str, the ground truth answer
    :pramrs: 'prediction': str, the model prediction
    :return: word_acc: float, the average word accuracy, computed by the edit distance between the answer and prediction
    :return: pair_acc: float, the average pair accuracy, computed by the number of correct pairs in the answer and prediction
    """
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

    return round(word_acc / float(len(results)), 4), round(pair_acc / float(len(results)), 4)






if __name__ == "__main__":
    for file in os.listdir("../decoder_lora/predict_data/"):
        if "predict_result" in file and ".txt" not in file:
            results = json.load(open("../decoder_lora/predict_data/" + file, "r", encoding="utf-8"))
            acc = compute_acc(results)
            print(f"测试结果文件 {file} 的精确度为 {acc}")
            
    for file in os.listdir("../decoder_fine_tuning/predict_data/"):
        if "predict_result" in file and ".txt" not in file:
            results = json.load(open("../decoder_fine_tuning/predict_data/" + file, "r", encoding="utf-8"))
            acc = compute_acc(results)
            print(f"测试结果文件 {file} 的精确度为 {acc}")
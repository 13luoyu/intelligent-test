import os
import json
from nltk.translate.bleu_score import sentence_bleu
from rouge import Rouge


def compute_char_wise_accuracy(predictions, labels):
    char_wise_accuracy = []
    for pred, label in zip(predictions, labels):
        dp = [[0 for _ in range(len(pred))] for _ in range(len(label))]
        for i in range(len(label)):
            for j in range(len(pred)):
                if i == 0 or j == 0:
                    if label[i] == pred[j]:
                        dp[i][j] = 1
                else:
                    if label[i] == pred[j]:
                        dp[i][j] = max(dp[i][j], dp[i-1][j], dp[i][j-1], dp[i-1][j-1] + 1)
                    else:
                        dp[i][j] = max(dp[i][j], dp[i-1][j], dp[i][j-1])
        char_wise_accuracy.append(dp[-1][-1] / len(label))
    return sum(char_wise_accuracy) / len(char_wise_accuracy)


def compute_word_wise_accuracy(predictions, labels):
    word_wise_accuracy = []
    for pred, label in zip(predictions, labels):

        label_words = []
        label = label.replace("\n", " ").split(" ")
        for i, l in enumerate(label):
            if l == "":
                continue
            if l == "and" or l == "if" or l == "then":
                label_words.append(f"{label[i+1]} {label[i+2]} {label[i+3]}")

        count = 0
        for word in label_words:
            if word in pred:
                count += 1
        word_wise_accuracy.append(count / len(label_words))

    return sum(word_wise_accuracy) / len(word_wise_accuracy)


def compute_cumulative_bleu(predictions, labels):
    cumulative_bleu = []
    for pred, label in zip(predictions, labels):
        pred = pred.replace("\n", " ").split(" ")
        label = label.replace("\n", " ").split(" ")
        bleu = sentence_bleu([label], pred, weights=(0.33, 0.33, 0.33, 0))
        cumulative_bleu.append(bleu)
    return sum(cumulative_bleu) / len(cumulative_bleu)


def compute_rouge_f1(predictions, labels):
    r = Rouge(metrics=["rouge-3"])
    rouge_scores = []
    for pred, label in zip(predictions, labels):
        rouge_score = r.get_scores(pred, label)
        # F1 score
        rouge_scores.append(rouge_score[0]['rouge-3']['f'])
    return sum(rouge_scores) / len(rouge_scores)


def eval(dir):
    result = open(f"{dir}eval.csv", "w", encoding="utf-8")
    result.write("Method,Char-wise Accuracy,Word-wise Accuracy,BLEU,Rouge\n")
    for file in os.listdir(dir):
        if file.endswith(".json"):
            data = json.load(open(f"{dir}{file}", "r", encoding="utf-8"))
            predictions = [d['prediction'] for d in data]
            labels = [d['label'] for d in data]
            print(f"Evaluating {file}...")
            char_wise_accuracy = compute_char_wise_accuracy(predictions, labels)
            print(f"Char-wise Accuracy: {char_wise_accuracy}")
            word_wise_accuracy = compute_word_wise_accuracy(predictions, labels)
            print(f"Word-wise Accuracy: {word_wise_accuracy}")
            cumulative_bleu = compute_cumulative_bleu(predictions, labels)
            print(f"BLEU: {cumulative_bleu}")
            rouge_f1 = compute_rouge_f1(predictions, labels)
            print(f"Rouge F1: {rouge_f1}")
            method = file.split("_")[0]
            result.write(f"{method},{char_wise_accuracy},{word_wise_accuracy},{cumulative_bleu},{rouge_f1}\n")



if __name__ == "__main__":
    eval("r2/")
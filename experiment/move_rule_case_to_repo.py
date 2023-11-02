import os
import shutil

if __name__ == "__main__":
    for file in os.listdir("data/"):
        if ".pdf" in file:
            shutil.copy(f"data/{file}", f"../rules_and_testcases/{file}")
    for file in os.listdir("rules_and_testcases"):
        shutil.copy(f"rules_and_testcases/{file}", f"../rules_and_testcases/{file}")


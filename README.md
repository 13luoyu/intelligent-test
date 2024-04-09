# LLM4Fin

LLM4Fin is a prototype tool for automatically generating test cases from natural language business rules. The process of LLM4Fin can be divided into three steps: **I**. Rule Extraction, **II**. Test Scenario Generation, **III**. Test Data Generation. The workflow is shown as below. Step I.1 and Step I.2 are performed by fine-tuned LLMs, and the other steps are implemented by well-designed algorithms. We evaluate it on real-world stock-trading software. Experimental results shows that LLM4Fin outperforms both general LLMs like ChatGPT and skilled testing engineers, on the business scenario coverage, code coverage, and time consumption. 

![Workflow of LLM4Fin](./figure/workflow.png)

## Project Structure 

> - **data/**.  Save the annotated data, training and verification data for fine-tuning LLMs, and the terminology base.
>   - *business_rules*. Save the annotated data.
>      - *json_for_sequence_classification/*. Save the annotated data for rule filtering task.
>           - *\*.json*. The rules that are not annotated.
>           - *finish_\*.json*. The rules that are annotated.
>      - *json_for_token_classification/*. Save the annotated data for rule element extraction task.
>           - *\*.json*. The rules that are not annotated.
>           - *finish_\*.json*. The rules that are annotated.
>      - *origin/*. Save the business rule documents in pdf format.
>      - *txt/*. Save the business rules in txt format.
>   - *knowledge.json*. The terminology base.
>   - *sc_\*.json*. The training and verification data for rule filtering task.
>   - *tc_\*.json*. The training and verification data for rule element extraction task.
>   - *tc_data.dict*. All the label used in rule element extraction task.
> - **log/**. Log directory.
> - **model/**. The model directory storage pre-trained models and fine-tuned models. Mengzi pre-trained models (mengzi-bert-base-fin) can be downloaded from [*https://github.com/Langboat/Mengzi*](https://github.com/Langboat/Mengzi). Our fine-tuned model can be downloaded from [https://huggingface.co/AnonymousAuthorsForISSTA2024/LLM4Fin](https://huggingface.co/AnonymousAuthorsForISSTA2024/LLM4Fin)
> - **ours/**.  Code for our three-step framework and fine-tuning the LLMs.
>   - *download_files/*. Save the business rule documents to be processed
>   - *cache/*. Save the intermediate and final outputs of our approach.
>   - *main.py*. Code for integrating and running the whole process.
>   - *process_knowledge.py*. Code for processing the domain knowledge and write into the terminology base.
>   - *process_nl_to_sci.py*. Code for Reading the business rule documents and dividing by sentence into the input of rule filtering sub-step.
>   - *process_sci_to_sco.py*. Code for rule filtering task.
>   - *process_sco_to_tci.py*. Code for transfering the output of rule filtering sub-step into the input of rule element extraction sub-step.
>   - *process_tci_to_tco.py*. Code for rule element extraction task.
>   - *process_tco_to_r1.py*. Code for rule assembly task.
>   - *process_r1_to_r2.py*. Code for operationalize rules task.
>   - *process_r2_to_r3.py*. Code for mine rule relations task.
>   - *process_r3_to_testcase.py*. Code for test data generation task.
>   - *process_testcase_to_outputs*. Code for reorganizing the generated test cases to a clear json format.
>   - *consistency_checking.py*. Code for consistency checking.
>   - *interface.py*. We package each step of the approach as an interface for the front-end to call.
>   - *sequence_classification.py*. Code for training and verifiying the LLMs for rule filtering task.
>   - *token_classification.py*. Code for training and verifiying the LLMs for rule element extraction task.
>   - *run_sequence_classification.sh*. Script for calling sequence_classification.py in different hyper-parameters to fine-tune models.
>   - *run_token_classification.sh*. Script for calling token_classification.py in different hyper-parameters to fine-tune models.
> - **support/**.  Code for corpus construction and compute model accuracy.
>   - *stopwords/*. Save the stopwords used in data augment.
>   - *analyse_sc_test_result.py*. Compute the accuracy of the predicted output of fine-tuned model for rule filtering task on validate dataset.
>   - *analyse_tc_test_result.py*. Compute the accuracy of the predicted output of fine-tuned model for rule element extraction task.
>   - *generate_data_for_sequence_classification.py*. Code for transfering business rule documents into a json format for rule element annotating
>   - *generate_data_for_token_classification.py*. Code for transfering business rule documents into a json format for rule element extraction annotating
>   - *check_tc_data.py*. Code for checking whether the annotated data is legal for rule element extraction.
>   - *integrate_data.py*. Code for integrating the annotated data and dividing them into training and validate dataset.
>   - *data_augment.py*. Code for data augment of the training dataset.
>   - *generate_dict_for_token_classification.py*. Read all the annotated data and get all the labels to generate *data/tc_data.dict*.
> - **transfer/**.  Code for rule format transformation.
>   - *mydsl_to_rules.py*. Code for transfering the rules in *mydsl* format to a data structure used in programs.
>   - *rules_to_mydsl.py*. Code for transfering the data structure used in programs to rules in *mydsl* format.
> - **utils/**.  Code for loading data and processing input parameters
>   - *arguments.py*.  Code for inputting hyperparameters and their default value settings in fine-tuning models.
>   - *data_loader.py*.  Code for loading data for model fine-tuning.
>   - *training_arguments.py*  Code for generating transformer.TrainingArguments, used in fine-tuning models.
>   - *try_gpu.py*  Return a gpu device if exists, otherwise a cpu device.
> - **requirements.txt**. Save the environmental dependence used in this project.
> - **setup.py**. Code for install our project. 


## Installation
Install step-by-step

    conda create -n intelligent-test python=3.9
    conda activate intelligent-test
    pip install -r requirements.txt
    pip install -e .

## Running
1. To fully run our tool, first download the fine-tuned model from [https://huggingface.co/AnonymousAuthorsForISSTA2024/LLM4Fin](https://huggingface.co/AnonymousAuthorsForISSTA2024/LLM4Fin) and saved the two models under **model/**, then run:

        cd ours
        python main.py
    
    The output file (textcase.json) and each intermediate outputs are saved under **ours/cache/**.

2. To fune-tune the model for rule filtering task, run

        cd ours
        nohup ./run_sequence_classification.sh >../log/run_sequence_classification.log &

    The training information such as loss are saved in **log/run_sequence_classification.log**. The verification results are saved in **sc_eval_{timestamp}.log**.

3. To fune-tune the model for rule element extraction task, run

        cd ours
        nohup ./run_token_classification.sh >../log/run_token_classification.log &
    
    The training information such as loss are saved in **log/run_token_classification.log**. The verification results are saved in **tc_eval_{timestamp}.log**.
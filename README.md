# LLM4Fin

LLM4Fin is a prototype tool for automatically generating test cases from natural language business rules. The process of LLM4Fin can be divided into three steps: **I**. Rule Extraction, **II**. Test Scenario Generation, **III**. Test Data Generation. The workflow is shown as below. Step I.1 and Step I.2 are performed by fine-tuned LLMs, and the other steps are implemented by well-designed algorithms. We evaluate it on real-world stock-trading software. Experimental results shows that LLM4Fin outperforms both general LLMs like ChatGPT and skilled testing engineers, on the business scenario coverage, code coverage, and time consumption. 

![Workflow of LLM4Fin](./figure/workflow.png)

## Project Structure 

### Data Directory

> - [**data/**](./data/).  The annotated data, training and validation dataset for fine-tuning LLMs, and the domain knowledge base.
>   - [**data_for_LLM_v1/**](./data/data_for_LLM_v1/). Data for method version 1. These datas are used to train bert-based autoencoding LLMs.
>       - [**business_rules/**](./data/data_for_LLM_v1/business_rules/). The annotated data.
>           - [**json_for_sequence_classification/**](./data/data_for_LLM_v1/business_rules/json_for_sequence_classification/). Save the annotated data for rule filtering task.
>               - *\*.json*. The rules that are not annotated.
>               - *finish_\*.json*. The rules that are annotated.
>           - [**json_for_token_classification/**](./data/data_for_LLM_v1/business_rules/json_for_token_classification/). Save the annotated data for rule element extraction task.
>               - *\*.json*. The rules that are not annotated.
>               - *finish_\*.json*. The rules that are annotated.
>           - [**origin/**](./data/data_for_LLM_v1/business_rules/origin/). Save the business rule documents in pdf format.
>           - [**txt/**](./data/data_for_LLM_v1/business_rules/txt/). Save the business rules in txt format.
>       - *sc_\*.json*. The training and verification data for rule filtering task.
>       - *tc_\*.json*. The training and verification data for rule element extraction task.
>       - [*tc_data.dict*](./data/data_for_LLM_v1/tc_data.dict). All the label used in rule element extraction task.
>       - [*rules.json*](./data/data_for_LLM_v1/rules.json). All the testable rules and their labels.
>   - [**data_for_LLM_v2/**](./data/data_for_LLM_v2/). Data for method version 2. These datas are used to train gpt-based autoregressive LLMs.
>       - *ir_\*_v1.csv*. Data transforme from [*data/data_for_LLM_v1/rules.json*](./data/data_for_LLM_v1/rules.json) and separate into train and validate datasets v1.
>       - [*ir_annotation_v2.json*](./data/data_for_LLM_v2/ir_annotation_v2.json). Annotated data for train autoregressive LLMs in a prompt-answer format. It is different from annotation v1 in the labels and annotation criteria.
>       - *ir_\*_v2.json*. Training and validate datasets separated from [*ir_annotation_v2.json*](./data/data_for_LLM_v2/ir_annotation_v2.json).
>       - *ir_\*_v2.csv*. Training and validate datasets v2 transformed from *ir_\*_v2.json*.
>   - [**data_for_LLM_v4/**](./data/data_for_LLM_v4/). Data for method version 4.
>       - [*annotation_v4.json*](./data/data_for_LLM_v4/annotation_v4.json). Annotated data for training autoregressive LLMs in a prompt-answer format. The answers are not rule elements but formal rules.
>       - *\*_v4.json*. Training and validate datasets separated from [*annotation_v4.json*](./data/data_for_LLM_v4/annotation_v4.json).
>       - *\*_v4.csv*. Training and validate datasets v4 transformed from *\*_v4.json*.
>   - [**domain_knowledge/**](./data/domain_knowledge/). The financial domain knowledge.
>       - [*knowledge.json*](./data/domain_knowledge/knowledge.json). The domain knowledge including is-a relation, has-a relation, and state machine.
>       - [*classification_knowledge.json*](./data/domain_knowledge/classification_knowledge.json). The well-organized has-a relation knowledge.
>       - [*classification_knowledge_tree.json*](./data/domain_knowledge/classification_knowledge_tree.json). The has-a relation knowledge in other format transformed from [*classification_knowledge.json*](./data/domain_knowledge/classification_knowledge.json).
>       - [*terms.txt*](./data/domain_knowledge/terms.txt). All the terms used in this project.


### Code for Fine-Tuning LLMs and Analyzing

> - [**decoder_fine_tuning/**](./decoder_fine_tuning/). The code and results for load datasets, fine-tune the gpt-based deocder LLMs and use the fine-tuned LLMs to interface.

> - [**decoder_lora/**](./decoder_lora/). The code and results for load datasets, use lora to train the gpt-based deocder LLMs and use the trained LLMs to interface.

> - [**encoder_fine_tuning/**](./encoder_fine_tuning/). The code and results for load datasets, fine-tune the bert-based encoder LLMs and use the fine-tuned LLMs to interface.

> - [**support/**](./support/).  Code for corpus construction and analyze model performance.
>   - [**stopwords/**](./support/stopwords/). Save the stopwords used in data augment.
>   - [*generate_data_for_decoder.py*](./support/generate_data_for_decoder.py). Code for transfering business rule documents into a json format for annotating for decoder LLMs.
>   - [*generate_data_for_sequence_classification.py*](./support/generate_data_for_sequence_classification.py). Code for transfering business rule documents into a json format for rule filtering annotating.
>   - [*generate_data_for_token_classification.py*](./support/generate_data_for_token_classification.py). Code for transfering business rule documents into a json format for rule element extraction annotating.
>   - [*check_tc_data.py*](./support/check_tc_data.py). Code for checking whether the annotated data is legal for rule element extraction.
>   - [*integrate_data.py*](./support/integrate_data.py). Code for integrating the annotated data and dividing them into training and validate dataset.
>   - [*data_augment.py*](./support/data_augment.py). Code for data augment of the training dataset.
>   - [*analyse_decoder_test_result.py*](./support/analyse_decoder_test_result.py). Compute the accuracy of the predicted output of trained decoder LLMs.
>   - [*analyse_sc_test_result.py*](./support/analyse_sc_test_result.py). Compute the accuracy of the predicted output of fine-tuned encoder LLMs for rule filtering task.
>   - [*analyse_tc_test_result.py*](./support/analyse_tc_test_result.py). Compute the accuracy of the predicted output of fine-tuned encoder LLMs for rule element extraction task.
>   - [*generate_dict_for_token_classification.py*](./support/generate_dict_for_token_classification.py). Read all the annotated data and get all the labels to generate [*data/data_for_LLM_v1/tc_data.dict*](./data/data_for_LLM_v1/tc_data.dict).
>   - [*generate_terms.py*](./support/generate_terms.py). Real all the annotated data and generate the terms base, saved at [*data/domain_knowledge/terms.py*](data/domain_knowledge/terms.txt).


### Code of Workflow

> - [**ours/**](./ours/).  Code for our three-step workflow. ***Method 1***.
>   - [*download_files/*](./ours/download_files/). The downloaded business rule documents to be processed.
>   - [*cache/*](./ours/cache/). The intermediate and final outputs of our approach.
>   - [*main.py*](./ours/main.py). Code for integrating and running the workflow.
>   - [*process_nl_to_sci.py*](./ours/process_nl_to_sci.py). Code for Reading the business rule documents and dividing by sentence into the input of rule filtering sub-step.
>   - [*process_sci_to_sco.py*](./ours/process_sci_to_sco.py). Code for rule filtering task.
>   - [*process_sco_to_tci.py*](./ours/process_sco_to_tci.py). Code for transfering the output of rule filtering sub-step into the input of rule element extraction sub-step.
>   - [*process_tci_to_tco.py*](./ours/process_tci_to_tco.py). Code for rule element extraction task.
>   - [*process_tco_to_r1.py*](./ours/process_tco_to_r1.py). Code for rule assembly task.
>   - [*process_r1_to_r2.py*](./ours/process_r1_to_r2.py). Code for operationalize rules task.
>   - [*process_r2_to_r3.py*](./ours/process_r2_to_r3.py). Code for mine rule relations task.
>   - [*process_r3_to_testcase.py*](./ours/process_r3_to_testcase.py). Code for test data generation task.
>   - [*process_testcase_to_outputs*](./ours/process_testcase_to_outputs.py). Code for reorganizing the generated test cases to a clear json format.
>   - [*process_knowledge.py*](./ours/process_knowledge.py). Code for processing the domain knowledge and write into the terminology base.
>   - [*consistency_checking.py*](./ours/consistency_checking.py). Code for consistency checking.
>   - [*interface.py*](./ours/interface.py). We package each step of the approach as an interface for the front-end to call.
> - [**transfer/**](./transfer/).  Code for rule format transformation.
>   - [*mydsl_to_rules.py*](./transfer/mydsl_to_rules.py). Code for transfering the rules in *mydsl* format to a data structure used in programs.
>   - [*rules_to_mydsl.py*](./transfer/rules_to_mydsl.py). Code for transfering the data structure used in programs to rules in *mydsl* format.
>   - [*knowledge_tree.py*](./transfer/knowledge_tree.py). Code for encode the has-a knowledge and decode it (Input: [*classification_knowledge*](./data/domain_knowledge/classification_knowledge.json), Output: [*classification_knowledge_tree*](./data/domain_knowledge/classification_knowledge_tree.json)), as well as select the domain knowledge desired.

### Experiment Directory

> - [**Experiment/**](./experiment/).

### Others

> - **requirements.txt**. Save the environmental dependence used in this project.
> - **setup.py**. Code for install our project. 
> - **model/**. The model directory storage pre-trained models and fine-tuned models. Mengzi pre-trained models (mengzi-bert-base-fin) can be downloaded from [*https://github.com/Langboat/Mengzi*](https://github.com/Langboat/Mengzi). Our fine-tuned model can be downloaded from [https://huggingface.co/AnonymousAuthorsForISSTA2024/LLM4Fin](https://huggingface.co/AnonymousAuthorsForISSTA2024/LLM4Fin)

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
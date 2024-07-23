#!/bin/bash

# run command: nohup ./run_token_classification.sh >../log/run_token_classification.log &


# 生成数据
# cd ..
# cd support
# python integrate_data.py
# python data_augment.py --task tc --nlpcda_size 20 --eda_tc_size 10
# cd ..
# cd ours

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ./output/tc --split \  --disable_tqdm True --model ../model/pretrained/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.002 --train_dataset ../data/data_for_LLM_encoder/tc_train_data_augmented.json --validate_dataset ../data/data_for_LLM_encoder/rules.json --learning_rate 2e-5

python token_classification.py --output_dir ./output/tc --split \  --disable_tqdm True --model ../model/pretrained/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.002 --train_dataset ../data/data_for_LLM_encoder/tc_train_data_augmented.json --validate_dataset ../data/data_for_LLM_encoder/rules.json --learning_rate 2e-5

python token_classification.py --output_dir ./output/tc --split \  --disable_tqdm True --model ../model/pretrained/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.002 --train_dataset ../data/data_for_LLM_encoder/tc_train_data_augmented.json --validate_dataset ../data/data_for_LLM_encoder/rules.json --learning_rate 2e-5



python token_classification.py --output_dir ./output/tc --split \  --disable_tqdm True --model ../model/pretrained/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.002 --train_dataset ../data/data_for_LLM_encoder/tc_train_data_augmented.json --validate_dataset ../data/data_for_LLM_encoder/rules.json --learning_rate 2e-5

python token_classification.py --output_dir ./output/tc --split \  --disable_tqdm True --model ../model/pretrained/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.002 --train_dataset ../data/data_for_LLM_encoder/tc_train_data_augmented.json --validate_dataset ../data/data_for_LLM_encoder/rules.json --learning_rate 2e-5

python token_classification.py --output_dir ./output/tc --split \  --disable_tqdm True --model ../model/pretrained/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.002 --train_dataset ../data/data_for_LLM_encoder/tc_train_data_augmented.json --validate_dataset ../data/data_for_LLM_encoder/rules.json --learning_rate 2e-5
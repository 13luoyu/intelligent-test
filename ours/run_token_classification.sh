#!/bin/bash

# run command: nohup ./run_token_classification.sh >../log/run_token_classification.log &

# 所有数据训练和验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_base.json --validate_dataset ../data/tc_validate_data_all.json

# 所有数据增强后训练和验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/tc_validate_data_all.json

# 所有数据训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_base.json --validate_dataset ../data/rules.json

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json

# 所有规则训练和验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_rules_base.json --validate_dataset ../data/tc_validate_data_rules.json

# 所有规则增强后训练和验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_rules_full.json --validate_dataset ../data/tc_validate_data_rules.json


# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.001

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts --weight_decay 0.001

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type polynomial --weight_decay 0.001

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant_with_warmup --weight_decay 0.001






# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type linear 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type polynomial 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant_with_warmup 
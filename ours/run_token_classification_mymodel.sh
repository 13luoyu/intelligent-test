#!/bin/bash

# nohup ./run_token_classification_mymodel.sh >../log/run_token_classification_mymodel.log &

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-1

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-1

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-1


python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-2

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-2

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-2


python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-3

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-3

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 1e-3
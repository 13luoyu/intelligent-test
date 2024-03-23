#!/bin/bash

# run command: nohup ./run_sequence_classification.sh >../log/run_sequence_classification.log &

# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task sc
cd ..
cd ours


python sequence_classification.py --output_dir ./output --split \  --disable_tqdm True --model ../model/pretrained/mengzi-bert-base-fin --num_train_epochs 50 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ./output --split \  --disable_tqdm True --model ../model/pretrained/mengzi-bert-base-fin --num_train_epochs 50 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ./output --split \  --disable_tqdm True --model ../model/pretrained/mengzi-bert-base-fin --num_train_epochs 50 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json




python sequence_classification.py --output_dir ./output --split \  --disable_tqdm True --model ../model/pretrained/bert_FinBERT --num_train_epochs 50 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ./output --split \  --disable_tqdm True --model ../model/pretrained/bert_FinBERT --num_train_epochs 50 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ./output --split \  --disable_tqdm True --model ../model/pretrained/bert_FinBERT --num_train_epochs 50 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json


#!/bin/bash

# run command: nohup ./run_sequence_classification.sh >../log/run_sequence_classification.log &

# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task sc
cd ..
cd ours

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model /mnt/d/XueZhiYi/XuanYuan2.0 --num_train_epochs 20 --lr_scheduler_type constant 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 10 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/sc_train_data_base.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 10 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/sc_train_data_base.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 10 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/sc_train_data_base.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 5 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 5 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 5 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json


# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type polynomial 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant_with_warmup 






# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 5 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 5 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 5 --lr_scheduler_type cosine --weight_decay 0.001 --train_dataset ../data/sc_train_data_full.json --validate_dataset ../data/sc_validate_data.json

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type polynomial 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant_with_warmup 
#!/bin/bash

# run command: nohup ./run_token_classification_2.sh >../log/run_token_classification.log &

# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task tc --nlpcda_size 10 --eda_tc_size 20
cd ..
cd ours

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json






# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task tc --nlpcda_size 10 --eda_tc_size 20
cd ..
cd ours

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json





# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task tc --nlpcda_size 10 --eda_tc_size 20
cd ..
cd ours

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json






# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task tc --nlpcda_size 10 --eda_tc_size 20
cd ..
cd ours

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json





# 生成数据
cd ..
cd support
python integrate_data.py
python data_augment.py --task tc --nlpcda_size 20 --eda_tc_size 30
cd ..
cd ours

# 所有数据增强后训练，规则验证
python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json
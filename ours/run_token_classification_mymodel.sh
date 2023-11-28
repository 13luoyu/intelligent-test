#!/bin/bash

# nohup ./run_token_classification_mymodel.sh >../log/run_token_classification_mymodel.log &

# cd ..
# cd support
# python integrate_data.py
# python data_augment.py --task tc --nlpcda_size 20 --eda_tc_size 10
# cd ..
# cd ours

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 2 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 5e-5

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 5e-5

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../train/model --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001 --train_dataset ../data/tc_train_data_all_full.json --validate_dataset ../data/rules.json --learning_rate 5e-5
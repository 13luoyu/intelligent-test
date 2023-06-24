#!/bin/bash

# run command: nohup ./run_token_classification.sh >../log/run_token_classification.log &


python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant --weight_decay 0.001

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear --weight_decay 0.001

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine --weight_decay 0.001

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts --weight_decay 0.001

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type polynomial --weight_decay 0.001

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant_with_warmup --weight_decay 0.001






# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type linear 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type polynomial 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant_with_warmup 
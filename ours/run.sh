#!/bin/bash

# run command: nohup ./run.sh >../log/ours/run.log &


python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type constant 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type linear 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type cosine 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type cosine_with_restarts 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type polynomial 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type constant_with_warmup 






python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type constant 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type linear 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type cosine 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type cosine_with_restarts 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type polynomial 

python main.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type constant_with_warmup 
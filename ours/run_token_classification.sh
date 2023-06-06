#!/bin/bash

# run command: nohup ./run_token_classification.sh >../log/ours/run_token_classification.log &


python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type constant 

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type linear 

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type cosine 

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type cosine_with_restarts 

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type polynomial 

python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 100 --lr_scheduler_type constant_with_warmup 






# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type constant 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type linear 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type cosine 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type cosine_with_restarts 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type polynomial 

# python token_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 100 --lr_scheduler_type constant_with_warmup 
#!/bin/bash

# run command: nohup ./run_sequence_classification.sh >../log/run_sequence_classification.log &

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model /mnt/d/XueZhiYi/XuanYuan2.0 --num_train_epochs 20 --lr_scheduler_type constant 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type linear 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type polynomial 

python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/mengzi-bert-base-fin --num_train_epochs 20 --lr_scheduler_type constant_with_warmup 






# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type linear 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type cosine_with_restarts 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type polynomial 

# python sequence_classification.py --output_dir ../model/ours --split \  --disable_tqdm True --model ../model/bert_FinBERT --num_train_epochs 20 --lr_scheduler_type constant_with_warmup 
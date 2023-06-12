#!/bin/bash

# run command: nohup ./run_mengzi.sh > run_mengzi_ir.log &


python information_retrieval.py --disable_tqdm True --num_train_epochs 10 --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

python information_retrieval.py --disable_tqdm True --num_train_epochs 30 --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model


python information_retrieval.py --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type linear --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

python information_retrieval.py --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type linear --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model


python information_retrieval.py --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type cosine --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

python information_retrieval.py --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type cosine --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model


python information_retrieval.py --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type cosine_with_restarts --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

python information_retrieval.py --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type cosine_with_restarts --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model


python information_retrieval.py --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type polynomial --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

python information_retrieval.py --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type polynomial --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model


python information_retrieval.py --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type constant_with_warmup --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

python information_retrieval.py --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type constant_with_warmup --model ../../model/mengzi-bert-base-fin --output_dir ir_mengzi_model

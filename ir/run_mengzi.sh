#!/bin/bash

# run command: nohup ./run_mengzi.sh >../log/mengzi/run_ir.log &


python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 10

python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 30


python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type linear

python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type linear


python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type cosine

python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type cosine


python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type cosine_with_restarts

python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type cosine_with_restarts


python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type polynomial

python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type polynomial


python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type constant_with_warmup

python information_retrieval.py --output_dir ../model/ir_mengzi --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type constant_with_warmup

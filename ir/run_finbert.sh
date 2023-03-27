#!/bin/bash

# run command: nohup ./run_finbert.sh >../log/finbert/run_ir.log &


python information_retrieval.py --model ../model/bert_FinBERT --output_dir ../model/ir_finbert --disable_tqdm True --num_train_epochs 10

python information_retrieval.py --model ../model/bert_FinBERT --output_dir ../model/ir_finbert --disable_tqdm True --num_train_epochs 30


python information_retrieval.py --model ../model/bert_FinBERT --output_dir ../model/ir_finbert --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type linear

python information_retrieval.py --model ../model/bert_FinBERT --output_dir ../model/ir_finbert --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type linear


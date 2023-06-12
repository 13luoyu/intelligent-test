#!/bin/bash

# run command: nohup ./run_finbert.sh > run_finbert_ir.log &


python information_retrieval.py --model ../../model/bert_FinBERT --disable_tqdm True --num_train_epochs 10 --output_dir ir_finbert_model

python information_retrieval.py --model ../../model/bert_FinBERT --disable_tqdm True --num_train_epochs 30 --output_dir ir_finbert_model


python information_retrieval.py --model ../../model/bert_FinBERT --disable_tqdm True --num_train_epochs 10 --lr_scheduler_type linear --output_dir ir_finbert_model

python information_retrieval.py --model ../../model/bert_FinBERT --disable_tqdm True --num_train_epochs 30 --lr_scheduler_type linear --output_dir ir_finbert_model


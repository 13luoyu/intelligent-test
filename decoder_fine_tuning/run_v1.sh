#!/bin/bash

# nohup bash run_v1.sh >../log/run_atom_fine_tuning.log &

output_dir=./output
# 需要修改到自己的输入目录
if [ ! -d ${output_dir} ];then  
    mkdir ${output_dir}
fi
python fine_tune_model.py \
    --model_name_or_path ../model/pretrained/Atom-7B \
    --train_files ../data/ir_train_v1.csv \
    --validation_files  ../data/ir_validate_v1.csv \
    --per_device_train_batch_size 1 \
    --per_device_eval_batch_size 1 \
    --do_train \
    --do_eval \
    --use_fast_tokenizer false \
    --output_dir ${output_dir} \
    --evaluation_strategy  steps \
    --max_eval_samples 800 \
    --learning_rate 1e-5 \
    --gradient_accumulation_steps 8 \
    --num_train_epochs 20 \
    --warmup_steps 400 \
    --logging_dir ${output_dir}/logs \
    --logging_strategy steps \
    --logging_steps 10 \
    --save_strategy steps \
    --preprocessing_num_workers 10 \
    --save_steps 100 \
    --eval_steps 100 \
    --save_total_limit 10 \
    --seed 42 \
    --ddp_find_unused_parameters false \
    --block_size 2048 \
    --report_to tensorboard \
    --overwrite_output_dir \
    --ignore_data_skip true \
    --bf16 \
    --gradient_checkpointing \
    --bf16_full_eval \
    --ddp_timeout 18000000 \
    --torch_dtype float16 \
    --test_output_file ./predict_data/test_result_framework.txt \
    --disable_tqdm true


python predict.py \
    --model_name_or_path ${output_dir}/best_model \
    --mode base \
    --tokenizer_fast false \
    --eval_dataset ../data/ir_validate.csv \
    --prediction_file ./predict_data/predict_result_base.json


python predict.py \
    --model_name_or_path ${output_dir}/best_model \
    --mode 8bit-base \
    --tokenizer_fast false \
    --eval_dataset ../data/ir_validate.csv \
    --prediction_file ./predict_data/predict_result_8bit-base.json
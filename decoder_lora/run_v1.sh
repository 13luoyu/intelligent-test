#!/bin/bash

# nohup bash run.sh >../log/run_llama2_lora.log &

# 模型保存目录、预测数据目录、训练数据文件、验证数据文件
output_dir=./output/v1
predict_dir=./predict_data/v1
train_files=../data/data_for_LLM_v2/ir_train_v1.csv
validation_files=../data/data_for_LLM_v2/ir_validate_v1.csv

# 如果文件不存在，创建
if [ ! -d ${output_dir} ];then  
    mkdir ${output_dir}
fi
if [ ! -d ${predict_dir} ];then  
    mkdir ${predict_dir}
fi

# 训练模型
python train_lora_model.py \
    --model_name_or_path ../model/pretrained/Atom-7B \
    --train_files ${train_files} \
    --validation_files ${validation_files} \
    --per_device_train_batch_size 1 \
    --per_device_eval_batch_size 1 \
    --do_train \
    --do_eval \
    --use_fast_tokenizer false \
    --output_dir ${output_dir} \
    --evaluation_strategy  steps \
    --max_eval_samples 800 \
    --learning_rate 1e-4 \
    --gradient_accumulation_steps 8 \
    --num_train_epochs 10 \
    --warmup_steps 400 \
    --load_in_bits 4 \
    --lora_r 8 \
    --lora_alpha 16 \
    --target_modules q_proj,k_proj,v_proj,o_proj,down_proj,gate_proj,up_proj \
    --logging_dir ${output_dir}/logs \
    --logging_strategy steps \
    --logging_steps 10 \
    --save_strategy steps \
    --preprocessing_num_workers 10 \
    --save_steps 100 \
    --eval_steps 100 \
    --save_total_limit 100 \
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
    --test_output_file ${predict_dir}/predict_result_framework.txt \
    --disable_tqdm true

# 合并lora模型和原始模型，原始模型4位量化
python merge.py \
    --adapter_model_name ${output_dir}/best_lora_model \
    --output_name ${output_dir}/best_model_4bit \
    --mode 4bit

# 使用4bit量化合并后的模型不量化加载预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_model_4bit \
#     --mode base \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_4bit_merge_normal_load.json

# 使用4bit量化合并后的模型以8bit加载预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_model_4bit \
#     --mode 8bit-base \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_4bit_merge_8bit_load.json


# 合并lora模型和原始模型，原始模型8位量化
# python merge.py \
#     --adapter_model_name ${output_dir}/best_lora_model \
#     --output_name ${output_dir}/best_model_8bit \
#     --mode 8bit

# 使用8bit量化合并后的模型不量化加载预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_model_8bit \
#     --mode base \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_8bit_merge_normal_load.json

# 使用8bit量化合并后的模型8bit量化加载预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_model_8bit \
#     --mode 8bit-base \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_8bit_merge_8bit_load.json


# 合并lora模型和原始模型，原始模型不量化
# python merge.py \
#     --adapter_model_name ${output_dir}/best_lora_model \
#     --output_name ${output_dir}/best_model

# 使用不量化合并后的模型不量化加载预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_model \
#     --mode base \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_normal_merge_normal_load.json

# 使用不量化合并后的模型8bit量化加载预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_model \
#     --mode 8bit-base \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_normal_merge_8bit_load.json



# 使用8bit加载原始模型并与lora运行时合并预测
# python predict.py \
#     --model_name_or_path ${output_dir}/best_lora_model \
#     --mode 8bit-lora \
#     --tokenizer_fast false \
#     --eval_dataset ${validation_files} \
#     --prediction_file ${predict_dir}/predict_result_8bit_load_lora.json

# 使用4bit加载原始模型并与lora运行时合并预测
#*******注意：这是和训练时的加载模式相同的模式********
python predict.py \
    --model_name_or_path ${output_dir}/best_lora_model \
    --mode 4bit-lora \
    --tokenizer_fast false \
    --eval_dataset ${validation_files} \
    --prediction_file ${predict_dir}/predict_result_4bit_load_lora.json

# 使用不加载原始模型并与lora运行时合并预测
python predict.py \
    --model_name_or_path ${output_dir}/best_lora_model \
    --mode lora \
    --tokenizer_fast false \
    --eval_dataset ${validation_files} \
    --prediction_file ${predict_dir}/predict_result_normal_load_lora.json



cd output
rm -rf checkpoint-*
cd ..
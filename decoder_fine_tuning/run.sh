#!/bin/bash

# nohup bash run.sh >../log/run_llama2_fine_tuning.log &

output_dir=./output/
predict_dir=./predict_data/
train_files=../data/data_for_LLM_decoder/ir_train.csv
validation_files=../data/data_for_LLM_decoder/ir_validate.csv
all_files=../data/data_for_LLM_decoder/ir_all.csv

# 需要修改到自己的输入目录
if [ ! -d ${output_dir} ];then  
    mkdir ${output_dir}
fi
if [ ! -d ${predict_dir} ];then  
    mkdir ${predict_dir}
fi

python fine_tune_model.py \
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
    --test_output_file ${predict_dir}/test_result_framework.txt \
    --disable_tqdm true


# 初始化一个空数组来存储所有文件的整数部分
file_numbers=()
# 这里的目录需要替换成你实际的目录
for file in $(find $output_dir -type d -name 'best_model_*' | grep -oP 'best_model_\K\d+'); do
    file_numbers+=("$file")
done
# 如果没有找到任何文件，则退出脚本
if [ ${#file_numbers[@]} -eq 0 ]; then
    echo "Error  没有找到匹配的文件。"
    exit 1
fi
# 使用sort和tail找到最大的整数
max_number=$(printf "%s\n" "${file_numbers[@]}" | sort -n | tail -1)
# 构建最大的文件名
filename="best_model_$max_number"


python predict.py \
    --model_name_or_path ${output_dir}/${filename} \
    --mode base \
    --tokenizer_fast false \
    --eval_dataset ${validation_files} \
    --prediction_file ${predict_dir}/predict_result_${filename}_base.json


python predict.py \
    --model_name_or_path ${output_dir}/${filename} \
    --mode base \
    --tokenizer_fast false \
    --eval_dataset ${all_files} \
    --prediction_file ${predict_dir}/predict_result_${filename}_base_all.json





cd ${output_dir}
rm -rf checkpoint-*
cd ..
cd ..
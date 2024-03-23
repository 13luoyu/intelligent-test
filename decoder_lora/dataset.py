import os
import random
import transformers
from datasets import load_dataset
from transformers.testing_utils import CaptureLogger



def get_raw_datasets(data_args, training_args, model_args):
    """
    获取原始的训练和验证数据
    """
    data_files, dataset_args = {}, {}
    # 获取训练、验证集名
    if data_args.train_files is not None:
        data_files['train'] = data_args.train_files
    if data_args.validation_files is not None:
        data_files['validation'] = data_args.validation_files
    # 获取扩展名(数据类型)
    extension = (data_args.train_files[0].split(".")[-1]
                 if data_args.train_files is not None
                 else data_args.validation_files.split(".")[-1]
        )
    if extension == "txt":
        extension = "text"
        dataset_args['keep_linebreaks'] = data_args.keep_linebreaks
    
    # 加载数据集
    raw_datasets = load_dataset(
        extension, 
        data_files=data_files, 
        cache_dir=os.path.join(training_args.output_dir, 'dataset_cache'), 
        use_auth_token=model_args.use_auth_token, 
        **dataset_args
    )

    # 如果不存在验证集，则将训练集数据分割为训练、验证集
    if "validation" not in raw_datasets.keys():
        raw_datasets['validation'] = load_dataset(
            extension, 
            data_files=data_files, 
            split=f"train[:{data_args.validation_split_percentage}%]", 
            cache_dir=model_args.cache_dir, 
            use_auth_token=model_args.use_auth_token, 
            **dataset_args
        )
        raw_datasets['train'] = load_dataset(
            extension, 
            data_files=data_files, 
            split=f"train[{data_args.validation_split_percentage}%:]", 
            cache_dir=model_args.cache_dir, 
            use_auth_token=model_args.use_auth_token, 
            **dataset_args
        )
    return raw_datasets



def get_tokenized_datasets(raw_datasets, tokenizer, training_args, data_args):
    """
    将原始的训练和验证数据tokenize
    """
    # 获取列名(csv首行名)
    if training_args.do_train:
        column_names = list(raw_datasets['train'].features)
    else:
        column_names = list(raw_datasets['validation'].features)
    
    # 判断csv是一列还是两列，并分别获取列名
    train_on_inputs = True
    if len(column_names) == 1:
        text_column_name = "text" if "text" in column_names else column_names[0]
    elif len(column_names) == 2:
        input_column_name = "input" if "input" in column_names else column_names[0]
        target_column_name = "target" if "target" in column_names else column_names[1]
        train_on_inputs = False
    else:
        raise ValueError("输入文件列数不对，应该为1列或2列")
    print(f"数据集中是否输入输出在同一列: {train_on_inputs}")

    # block_size为一个句子的最长长度
    if data_args.block_size is None:
        block_size = tokenizer.model_max_length
        if block_size > 2048:
            block_size = 2048
    else:
        block_size = min(data_args.block_size, tokenizer.model_max_length)

    # since this will be pickled to avoid _LazyModule error in Hasher force logger loading before tokenize_function
    tok_logger = transformers.utils.logging.get_logger("transformers.tokenization_utils_base")

    def tokenize_function(examples):
        """
        对一列的数据，将其tokenize，input_ids和labels相同
        """
        with CaptureLogger(tok_logger) as cl:
            output = tokenizer(
                [item for item in examples[text_column_name]],
                truncation=True,
                max_length=block_size,
                padding=False,
                return_tensors=None
            )
            output['labels'] = output['input_ids'].copy()
        return output
    
    def tokenize(prompt):
        """
        tokenize一个句子
        """
        result = tokenizer(
            prompt,
            truncation=True,
            max_length=block_size,
            padding=False,
            return_tensors=None
        )
        result['labels'] = result['input_ids'].copy()
        return result
    
    def generate_and_tokenize_prompt(data_point):
        """
        两列的句子，tokenize后进行掩码
        """
        input_text = data_point[input_column_name]
        target_text = data_point[target_column_name]
        full_prompt = input_text + target_text
        tokenized_full_prompt = tokenize(full_prompt)
        if not train_on_inputs:
            user_prompt = input_text
            tokenized_user_prompt = tokenize(user_prompt)
            user_prompt_len = len(tokenized_user_prompt['input_ids'])
            tokenized_full_prompt['labels'] = [-100] * user_prompt_len + tokenized_full_prompt['labels'][user_prompt_len:]
        return tokenized_full_prompt
    
    # tokenize数据集所有句子
    with training_args.main_process_first(desc="dataset map tokenization"):
        if not data_args.streaming:
            tokenized_datasets = raw_datasets.map(
                tokenize_function if train_on_inputs == True else generate_and_tokenize_prompt,
                batched=True if train_on_inputs == True else False,
                num_proc = data_args.preprocessing_num_workers,
                remove_columns = column_names,
                load_from_cache_file = not data_args.overwrite_cache,
                desc = "Running tokenizer on dataset"
            )
        else:
            tokenized_datasets = raw_datasets.map(
                tokenize_function if train_on_inputs == True else generate_and_tokenize_prompt,
                batched=True if train_on_inputs == True else False,
                remove_columns = column_names
            )

    return tokenized_datasets


def load_datasets(data_args, training_args, model_args, tokenizer, logger):
    """
    加载数据集，分为训练集与验证集，并执行tokenize
    """
    raw_datasets = get_raw_datasets(data_args, training_args, model_args)
    tokenized_datasets = get_tokenized_datasets(raw_datasets, tokenizer, training_args, data_args)
    train_dataset, eval_dataset = None, None

    # 训练集限制大小，并且打乱
    if training_args.do_train:
        if "train" not in tokenized_datasets:
            raise ValueError("--do_train 对应的训练数据集未设置")
        
        train_dataset = tokenized_datasets['train']
        if data_args.max_train_samples is not None:
            max_train_samples = min(len(train_dataset), data_args.max_train_samples)
            train_dataset = train_dataset.select(range(max_train_samples))
        for index in random.sample(range(len(train_dataset)), 1):
            logger.info(f"训练集的采样{index}: {train_dataset[index]}")
        train_dataset = train_dataset.shuffle(seed=training_args.seed)
    # 验证集限制大小
    if training_args.do_eval:
        if "validation" not in tokenized_datasets:
            raise ValueError("--do_eval 对应的验证数据集未设置")
        
        eval_dataset = tokenized_datasets['validation']
        if data_args.max_eval_samples is not None:
            max_eval_samples = min(len(eval_dataset), data_args.max_eval_samples)
            eval_dataset = eval_dataset.select(range(max_eval_samples))
        
    return train_dataset, eval_dataset


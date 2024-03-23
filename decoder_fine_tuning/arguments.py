import sys
import os

from dataclasses import dataclass, field
from typing import Optional, List
from transformers import MODEL_FOR_CAUSAL_LM_MAPPING, HfArgumentParser, TrainingArguments
from transformers.utils.versions import require_version

MODEL_CONFIG_CLASSES = list(MODEL_FOR_CAUSAL_LM_MAPPING.keys())
MODEL_TYPES = tuple(conf.model_type for conf in MODEL_CONFIG_CLASSES)



@dataclass
class ModelArguments:
    """
    模型加载和微调训练相关参数
    """
    # 模型路径
    model_name_or_path: Optional[str] = field(default=None, metadata={"help":"包含模型权重的检查点。如果想从头训练模型，不要设置此参数"})

    # 模型类型，如bert, gpt2, llama, ...
    model_type: Optional[str] = field(default=None, metadata={"help":"如果从头训练，需要设置此参数。参数可选值为: " + ", ".join(MODEL_TYPES)})

    # 
    config_overrides: Optional[str] = field(default=None, metadata={"help":"如果从头训练，重写一些默认设置。例子: n_embed=10,resid_pdrop=0.2,cale_attn_weights=false,summary_type=cls_index"})

    config_name: Optional[str] = field(default=None, metadata={"help":"预训练的配置名或路径，如果与model_name_or_path不一致，需要设置此参数"})

    tokenizer_name: Optional[str] = field(default=None, metadata={"help":"预训练的tokenizer名或路径，如果与model_name_or_path不一致，需要设置此参数"})

    cache_dir: Optional[str] = field(default=None, metadata={"help":"缓存目录，存放日志、训练好的模型等"})

    use_fast_tokenizer: bool = field(default=True, metadata={"help":"是否使用一个由tokenizer库支持的快速tokenizer"})
    
    torch_dtype: Optional[str] = field(default=None, metadata={"help":"重写默认的`torch.dtype`并且以此dtype加载模型。如果设置为`auto`，则默认以模型权重的dtype加载模型", "choices": ["auto", "bfloat16", "float16", "float32"]})

    model_revision: str = field(default="main", metadata={"help":"要使用的模型版本(可以是分支名、标签名、commit id等)"})

    use_auth_token: bool = field(default=False, metadata={"help":"身份验证令牌。当使用huggingface的非公开模型、数据等内容时，需要设置此参数"})

    load_in_bits: Optional[int] = field(default=8)

    
    def __post_init__(self):
        """验证参数设置的正确性"""
        # --config_overrides不能与--config_name或--model_name_or_path组合使用
        if self.config_overrides is not None and (self.config_name is not None or self.model_name_or_path is not None):
            raise ValueError("--config_overrides 不能和 --config_name 或 --model_name_or_path 一起使用")






@dataclass
class DataTrainingArguments:
    """
    模型训练和验证所需的数据集相关参数
    """

    train_on_inputs: bool = field(default=False, metadata={"help":"如果要使用datasets库中的数据集，是否重写之前下载(如果有)的数据集"})

    dataset_name: Optional[str] = field(default=None, metadata={"help":"如果要使用datasets库中的数据集，设置此参数指定要使用的数据集名"})

    dataset_config_name: Optional[str] = field(default=None, metadata={"help":"如果要使用datasets库中的数据集，设置此参数指定要使用的数据集配置名"})

    train_files: Optional[List[str]] = field(default=None, metadata={"help":"训练数据集(一个或多个文本文件)"})

    validation_files: Optional[List[str]] = field(default=None, metadata={"help":"验证数据集(一个或多个文本文件)"})

    max_train_samples: Optional[int] = field(default=None, metadata={"help":"为了debug或更快训练，如果设置，将训练集数目截断为该值"})

    max_eval_samples: Optional[int] = field(default=None, metadata={"help":"为了debug或更快训练，如果设置，将验证集数目截断为该值"})

    streaming: bool = field(default=False, metadata={"help":"启用流模式"})

    block_size: Optional[int] = field(default=None, metadata={"help":"tokenization之后的输入序列长度，默认为最长的句子的长度(包含特殊token)，训练集中超过此长度的句子将被截断"})

    overwrite_cache: bool = field(default=False, metadata={"help":"是否重写缓存的训练和验证集"})

    validation_split_percentage: Optional[int] = field(default=5, metadata={"help":"当没有验证集时，将百分之多少的训练集分割出来作为验证集"})

    preprocessing_num_workers: Optional[int] = field(default=None, metadata={"help":"读取和处理数据所用的线程数"})

    keep_linebreaks: bool = field(default=True, metadata={"help":"当使用txt文件时，是否保留换行符"})

    test_output_file: Optional[str] = field(default=None, metadata={"help":"预测保存的位置"})

    def __post_init__(self):
        if self.streaming:
            require_version("datasets>=2.0.0", "流模型要求`datasets>=2.0.0`")
        if self.dataset_name is None and self.train_files is None and self.validation_files is None:
            raise ValueError("--dataset_name, --train_files 和 --validation_files 都没有设置，未指定数据集")
        else:
            if self.train_files is not None:
                file_extension = self.train_files[0].split(".")[-1]
                assert file_extension in ["csv", "json", "txt"], "`train_file` 应该是csv, json或txt格式的文件"
            if self.validation_files is not None:
                file_extension = self.validation_files[0].split(".")[-1]
                assert file_extension in ["csv", "json", "txt"], "`validation_file` 应该是csv, json或txt格式的文件"





def get_arguments():
    """
    解析命令行参数，返回模型设置、数据设置和训练设置
    """
    parser = HfArgumentParser((ModelArguments, DataTrainingArguments, TrainingArguments))

    # 如果命令行附加参数为一个json文件，这个json文件就包含所有的配置参数，否则，从命令行一个一个读入
    if len(sys.argv) == 2 and sys.argv[1].endswith(".json"):
        # 执行这个分支所需的命令为: 
        # python main.py args.json
        model_args, data_args, training_args = parser.parse_json_file(json_file=os.path.abspath(sys.argv[1]))
    else:
        # 执行这个分支所需的命令为: 
        # python main.py --model_name_or_path model/Atom-7B --train_files data/train_sft.csv ...
        model_args, data_args, training_args = parser.parse_args_into_dataclasses()
    
    return model_args, data_args, training_args
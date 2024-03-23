import os
from transformers.trainer_utils import get_last_checkpoint
from transformers import AutoConfig, CONFIG_MAPPING, AutoTokenizer, BitsAndBytesConfig, AutoModelForCausalLM
from peft import LoraConfig, PeftModel, get_peft_model, prepare_model_for_int8_training, prepare_model_for_kbit_training
import torch


def judge_and_get_last_checkpoint(training_args, logger):
    """
    获取上次训练的最后一个模型的checkpoint
    """
    last_checkpoint = None
    # 如果output_dir存在，并且是训练，且设置了不重写output_dir，则尝试加载checkpoint，继续训练
    if os.path.isdir(training_args.output_dir) and training_args.do_train and not training_args.overwrite_output_dir:
        last_checkpoint = get_last_checkpoint(training_args.output_dir)
        # 这个目录没有checkpoint，是无关内容，需要设置重写
        if last_checkpoint is None and len(os.listdir(training_args.output_dir)) > 0:
            raise ValueError(f"输出目录({training_args.output_dir})已经存在并且不为空，请设置 --overwrite_output_dir 来覆盖原目录")
        elif last_checkpoint is not None and training_args.resume_from_checkpoint is None:
            logger.info(f"发现checkpoint，在{last_checkpoint}上继续训练。如果你想要从头训练，改变或清空 --output_dir 对应位置，或者设置 --overwrite_output_dir")
    return last_checkpoint


# AutoConfig.from_pretrained(
#   pretrained_model_name_or_path (str, optional), 指定要加载的预训练模型的名称或路径。这可以是模型的名称（例如，'bert-base-uncased'），也可以是模型的本地路径。
#   cache_dir (str, optional), 指定用于缓存预训练模型配置文件的目录路径。如果设置为 `None`，将使用默认缓存目录。
#   force_download (bool, optional), 如果设置为 `True`，将强制重新下载模型配置，覆盖任何现有的缓存。
#   resume_download (bool, optional), 这是可选参数，如果设置为 True，则在下载过程中重新开始下载，即使部分文件已经存在。
#   proxies (Dict[str, str], optional), 这是一个字典，用于指定代理服务器的设置。代理服务器允许您在访问互联网资源时通过中继服务器进行请求，这对于在受限网络环境中使用 Transformers 库来加载模型配置信息非常有用。例如proxies = { "http": "http://your_http_proxy_url", "https": "https://your_https_proxy_url" }
#   revision (str, optional), 指定要加载的模型的 Git 版本（通过提交哈希）
#   return_unused_kwargs (bool, optional, 默认值为 False),  如果将此参数设置为 True，函数将返回未使用的配置参数。这对于识别和检查传递给函数的不受支持或未识别的参数很有用
#   trust_remote_code (bool, optional, 默认值为 False), 默认情况下，trust_remote_code 设置为 True。这意味着当您使用 from_pretrained() 方法加载模型配置文件时，它将下载来自 Hugging Face 模型中心或其他在线资源的配置文件。这是一个方便的默认行为，因为通常这些配置文件是由官方提供的，且是可信的。如果您将 trust_remote_code 设置为 False，则表示您不信任从远程下载的配置文件，希望加载本地的配置文件。这对于安全性或定制性要求较高的场景可能是有用的。在这种情况下，您需要提供一个本地文件路径，以明确指定要加载的配置文件
#   **kwargs,  其他配置参数，具体取决于所选择的预训练模型类型。这些参数可以因模型而异
# )


def get_model_config(model_args, logger):
    """
    加载或创建模型config
    """
    config_kwargs = {
        "cache_dir": model_args.cache_dir,
        "revision": model_args.model_revision,
        "use_auth_token": model_args.use_auth_token
    }
    # 如果存在预训练模型或配置，加载配置，否则重新创建配置
    if model_args.config_name:
        config = AutoConfig.from_pretrained(model_args.config_name, **config_kwargs)
    elif model_args.model_name_or_path:
        config = AutoConfig.from_pretrained(model_args.model_name_or_path, **config_kwargs)
    else:
        config = CONFIG_MAPPING[model_args.model_type]()
        logger.warning("你正在从头开始创建一个新的配置")
        if model_args.config_overrides is not None:
            logger.info(f"--config_overrides 参数设置，重写的配置包括: {model_args.config_overrides}")
            config.update_from_string(model_args.config_overrides)
            logger.info(f"新的配置: {config}")
    return config


# AutoTokenizer.from_pretrained(
#   pretrained_model_name_or_path (str), 指定要加载的预训练模型的名称或路径。可以是模型名称（例如 "bert-base-uncased"）或模型文件夹的路径
#   inputs (additional positional arguments, optional), 可选，额外的位置参数，这些参数会传递给标记器（Tokenizer）的__init__()方法。这允许你进一步自定义标记器的初始化
#   config ([PretrainedConfig], optional), 这个配置对象用于确定要实例化的分词器类
#   force_download (bool, optional),
#   resume_download (bool, optional),
#   proxies (Dict[str, str], optional),
#   revision (str, optional),
#   subfolder (str, optional), 如果相关文件位于 huggingface.co 模型仓库的子文件夹内（例如 facebook/rag-token-base），请在这里指定
#   use_fast (bool, optional, 默认True), 这是一个布尔值，指示是否强制使用 fast tokenizer，即使其不支持特定模型的功能。默认为 True
#   tokenizer_type (str, optional), 参数用于指定要实例化的分词器的类型
#   trust_remote_code (bool, optional 默认False)
# )




def get_tokenizer(model_args):
    """
    加载或创建模型tokenizer
    """
    tokenizer_kwargs = {
        "cache_dir": model_args.cache_dir,
        "use_fast": model_args.use_fast_tokenizer,
        "revision": model_args.model_revision,
        "use_auth_token": model_args.use_auth_token,
        "padding_side": "left"  # 生成式模型不同于bert等模型，通常使用左填充
    }
    # 比如：输入，我喜欢吃苹果 。
    # 期望预测和生成的内容：我喜欢吃苹果，因为它很好吃。
    # 右填充模型输入：我喜欢吃苹果[pad] [pad]，输出：我喜欢吃苹果[pad] [pad]，因为它很好吃。
    # 左填充模型输入：[pad] [pad]我喜欢吃苹果，输出：[pad] [pad]我喜欢吃苹果，因为它很好吃。
    # [pad] 卡在文本中间，这会造成模型生成的结果可能会很差。

    # 加载tokenizer
    if model_args.tokenizer_name:
        tokenizer = AutoTokenizer.from_pretrained(model_args.tokenizer_name, **tokenizer_kwargs)
    elif model_args.model_name_or_path:
        tokenizer = AutoTokenizer.from_pretrained(model_args.model_name_or_path, **tokenizer_kwargs)
    else:
        raise ValueError("你正在从头开始创建一个新的tokenizer，而本代码不支持此功能。你可以另外创建tokenizer，保存它，并且设置 --tokenizer_name 参数为其路径")
    tokenizer.pad_token = tokenizer.eos_token
    print(tokenizer.eos_token)
    return tokenizer



def get_lora_config(model_args, logger):
    """
    获取lora模型配置
    """
    lora_config = LoraConfig(
        r=model_args.lora_r,  # 低秩矩阵的秩
        lora_alpha=model_args.lora_alpha,  # 缩放指数（ΔWx * α / r）
        target_modules=model_args.target_modules,  # lora训练模块
        fan_in_fan_out=False,
        lora_dropout=0.05,  # dropout
        inference_mode=False,
        bias="none",
        task_type="CAUSAL_LM"
    )
    logger.info(f"lora配置: {lora_config}")
    return lora_config


def get_bnb_config():
    """
    获取bitsandbtyes配置
    """
    bnb_config = BitsAndBytesConfig(
        load_in_4bit=True,  # 4位量化
        bnb_4bit_use_double_quant=True,  # 此标志用于嵌套量化，其中第一次量化的量化常数再次量化
        bnb_4bit_quant_type="nf4",  # 设置 bnb.nn.Linear4Bit 层中的量化数据类型。选项是 FP4 和 NF4 数据类型，由 fp4 或 nf4 指定。
        bnb_4bit_compute_dtype=torch.bfloat16  # 设置计算类型
    )
    return bnb_config




def load_model_and_tokenizer(model_args, logger):
    """
    加载预训练模型和tokenizer
    """
    config = get_model_config(model_args, logger)
    tokenizer = get_tokenizer(model_args)
    lora_config = get_lora_config(model_args, logger)
    bnb_config = get_bnb_config()

    if model_args.model_name_or_path:
        torch_dtype = (
            model_args.torch_dtype
            if model_args.torch_dtype in ["auto", None]
            else getattr(torch, model_args.torch_dtype)
        )
        logger.info(f"torch_dtype: {torch_dtype}")

        #  Llama只支持8bit量化，即可以指定load_in_8bit=True
        #  4bit量化需要配置，即quantization_config
        model = AutoModelForCausalLM.from_pretrained(
            model_args.model_name_or_path,
            from_tf=bool(".ckpt" in model_args.model_name_or_path),
            config=config,
            cache_dir = model_args.cache_dir,
            revision=model_args.model_revision,
            use_auth_token=model_args.use_auth_token,
            torch_dtype=torch_dtype,
            load_in_8bit=True if model_args.load_in_bits==8 else False,
            trust_remote_code=True,
            use_flash_attention_2=True,
            quantization_config=bnb_config if model_args.load_in_bits==4 else None,
            device_map={"": int(os.environ.get("LOCAL_RANK") or 0)}
            # device_map = 'auto'
        )
    else:
        model = AutoModelForCausalLM.from_config(config)
        n_params = sum({p.data_ptr(): p.numel() for p in model.parameters()}.values())
        logger.info(f"从头训练新的模型，包含参数量为{n_params/2**20:.2f}M")
    
    # 修改embedding输入层大小
    embedding_size = model.get_input_embeddings().weight.shape[0]
    if len(tokenizer) > embedding_size:
        model.resize_token_embeddings(len(tokenizer))
    
    if model_args.load_in_bits == 8:
        model = prepare_model_for_int8_training(model)
    if model_args.load_in_bits == 4:
        model = prepare_model_for_kbit_training(model)
    
    model = get_peft_model(model, lora_config)
    model.print_trainable_parameters()

    return model, tokenizer



import logging
import sys
import transformers
import datasets

# 日志有下列几个级别
# 50 `transformers.logging.CRITICAL` or `transformers.logging.FATAL`
# 40 `transformers.logging.ERROR`
# 30 `transformers.logging.WARNING` or `transformers.logging.WARN`
# 20 `transformers.logging.INFO`
# 10 `transformers.logging.DEBUG`
# 默认级别为30

def get_logger(training_args):
    """
    获得一个日志管理器
    """
    logger = logging.getLogger(__name__)
    logging.basicConfig(
        format="%(asctime)s - %(levelname)s - %(name)s - %(message)s",
        datefmt="%m/%d/%Y %H:%M:%S",
        handlers=[logging.StreamHandler(sys.stdout)],
    )
    # 设置transformers库的日志级别为info(20)
    if training_args.should_log:
        transformers.utils.logging.set_verbosity_info()
    
    log_level = training_args.get_process_log_level()
    logger.setLevel(log_level)
    datasets.utils.logging.set_verbosity(log_level)
    transformers.utils.logging.set_verbosity(log_level)
    transformers.utils.logging.enable_default_handler()
    transformers.utils.logging.enable_explicit_format()

    return logger
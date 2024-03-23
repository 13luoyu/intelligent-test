from decoder_fine_tuning.arguments import get_arguments
from decoder_fine_tuning.log import get_logger
from decoder_fine_tuning.model import judge_and_get_last_checkpoint, load_model_and_tokenizer
from decoder_fine_tuning.dataset import load_datasets
from decoder_fine_tuning.train import train_model
from transformers import set_seed

def main():
    model_args, data_args, training_args = get_arguments()
    logger = get_logger(training_args)

    logger.warning(
        f"Process rank: {training_args.local_rank}, device: {training_args.device}, n_gpu: {training_args.n_gpu}"
        + f"distributed training: {bool(training_args.local_rank != -1)}, 16-bits training: {training_args.fp16}"
    )
    logger.info(f"Training/evaluation parameters {training_args}")

    set_seed(training_args.seed)

    last_checkpoint = judge_and_get_last_checkpoint(training_args, logger)

    model, tokenizer = load_model_and_tokenizer(model_args, logger)

    train_dataset, eval_dataset = load_datasets(data_args, training_args, model_args, tokenizer, logger)

    train_model(model, last_checkpoint, tokenizer, train_dataset, eval_dataset, training_args, data_args, logger)



if __name__ == "__main__":
    main()
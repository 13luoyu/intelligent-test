import argparse




def arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default="../model/mengzi-bert-base-fin")
    parser.add_argument("--num_train_epochs", type=int, default=10)
    parser.add_argument("--per_device_train_batch_size", type=int, default=8)
    parser.add_argument("--per_device_eval_batch_size", type=int, default=8)
    parser.add_argument("--logging_step", type=int, default=100)
    parser.add_argument("--evaluation_strategy", type=str, default="epoch")
    # parser.add_argument("--eval_steps", type=int, default=500)
    parser.add_argument("--load_best_model_at_end", type=bool, default=True)
    parser.add_argument("--learning_rate", type=float, default=1e-5)
    parser.add_argument("--output_dir", type=str, default="../model/model")
    parser.add_argument("--save_total_limit", type=int, default=5)
    parser.add_argument("--lr_scheduler_type", type=str, default="constant")
    parser.add_argument("--gradient_accumulation_steps", type=int, default=1)
    parser.add_argument("--dataloader_num_workers", type=int, default=4)
    parser.add_argument("--remove_unused_columns", type=bool, default=False)
    parser.add_argument("--logging_dir", type=str, default="../log/log.log")
    parser.add_argument("--save_strategy", type=str, default="epoch")
    parser.add_argument("--disable_tqdm", type=bool, default=False)
    parser.add_argument("--split", type=str, default="\x02")
    parser.add_argument("--weight_decay", type=float, default=0.0)
    parser.add_argument("--sentence_max_length", type=int, default=512)
    parser.add_argument("--train_dataset", type=str, default="../data/tc_train_data_rules_base.json")
    parser.add_argument("--validate_dataset", type=str, default="../data/tc_validate_data_rules.json")
    paras = parser.parse_args()
    paras_dict = vars(paras)
    return paras_dict
from transformers import Seq2SeqTrainingArguments, TrainingArguments


def get_training_arguments(training_args):
    num_train_epochs = training_args["num_train_epochs"]
    per_device_train_batch_size = training_args["per_device_train_batch_size"]
    per_device_eval_batch_size = training_args["per_device_eval_batch_size"]
    logging_step = training_args["logging_step"]
    evaluation_strategy = training_args["evaluation_strategy"]
    # eval_steps = training_args["eval_steps"]
    load_best_model_at_end = training_args["load_best_model_at_end"]
    learning_rate = training_args["learning_rate"]
    output_dir = training_args["output_dir"]
    save_total_limit = training_args["save_total_limit"]
    lr_scheduler_type = training_args["lr_scheduler_type"]
    gradient_accumulation_steps = training_args["gradient_accumulation_steps"]
    dataloader_num_workers = training_args["dataloader_num_workers"]
    remove_unused_columns = training_args["remove_unused_columns"]
    logging_dir = training_args["logging_dir"]
    save_strategy = training_args["save_strategy"]
    disable_tqdm = training_args["disable_tqdm"]
    weight_decay = training_args["weight_decay"]

    training_args = TrainingArguments(
        num_train_epochs=num_train_epochs,
        per_device_train_batch_size=per_device_train_batch_size,
        per_device_eval_batch_size=per_device_eval_batch_size,
        logging_steps=logging_step,
        evaluation_strategy=evaluation_strategy,
        # eval_steps=eval_steps,
        load_best_model_at_end=load_best_model_at_end,
        learning_rate=learning_rate,
        output_dir=output_dir,
        save_total_limit=save_total_limit,
        lr_scheduler_type=lr_scheduler_type,
        gradient_accumulation_steps=gradient_accumulation_steps,
        dataloader_num_workers=dataloader_num_workers,
        remove_unused_columns=remove_unused_columns,
        logging_dir=logging_dir,
        save_strategy=save_strategy,
        disable_tqdm=disable_tqdm,
        weight_decay=weight_decay
    )
    return training_args


def get_seq2seq_training_arguments(training_args):
    num_train_epochs = training_args["num_train_epochs"]
    per_device_train_batch_size = training_args["per_device_train_batch_size"]
    per_device_eval_batch_size = training_args["per_device_eval_batch_size"]
    logging_step = training_args["logging_step"]
    evaluation_strategy = training_args["evaluation_strategy"]
    eval_steps = training_args["eval_steps"]
    load_best_model_at_end = training_args["load_best_model_at_end"]
    learning_rate = training_args["learning_rate"]
    output_dir = training_args["output_dir"]
    save_total_limit = training_args["save_total_limit"]
    lr_scheduler_type = training_args["lr_scheduler_type"]
    gradient_accumulation_steps = training_args["gradient_accumulation_steps"]
    dataloader_num_workers = training_args["dataloader_num_workers"]
    remove_unused_columns = training_args["remove_unused_columns"]
    logging_dir = training_args["logging_dir"]
    save_strategy = training_args["save_strategy"]
    disable_tqdm = training_args["disable_tqdm"]

    training_args = Seq2SeqTrainingArguments(
        num_train_epochs=num_train_epochs,
        per_device_train_batch_size=per_device_train_batch_size,
        per_device_eval_batch_size=per_device_eval_batch_size,
        logging_steps=logging_step,
        evaluation_strategy=evaluation_strategy,
        eval_steps=eval_steps,
        load_best_model_at_end=load_best_model_at_end,
        learning_rate=learning_rate,
        output_dir=output_dir,
        save_total_limit=save_total_limit,
        lr_scheduler_type=lr_scheduler_type,
        gradient_accumulation_steps=gradient_accumulation_steps,
        dataloader_num_workers=dataloader_num_workers,
        remove_unused_columns=remove_unused_columns,
        logging_dir=logging_dir,
        save_strategy=save_strategy,
        disable_tqdm=disable_tqdm,
        predict_with_generate=True,
        fp16=True
    )
    return training_args
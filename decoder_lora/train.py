import os
import math
import sys
import transformers
import evaluate
import torch
import bitsandbytes as bnb
from transformers import Trainer, TrainerCallback
from transformers.trainer_utils import PREFIX_CHECKPOINT_DIR
from peft import PeftModel, set_peft_model_state_dict
import time


def get_optimizer(model, training_args):
    optimizer_kwargs = {
        "lr": training_args.learning_rate,
        "betas": (training_args.adam_beta1, training_args.adam_beta2),
        "eps": training_args.adam_epsilon
    }
    adam_bnb_optim = bnb.optim.AdamW32bit(model.parameters(), **optimizer_kwargs)
    return adam_bnb_optim

def preprocess_logits_for_metrics(logits, labels):
    # Depending on the model and config, logits may contain extra tensors, like past_key_values, but logits always come first.
    if isinstance(logits, tuple):
        logits = logits[0]
    return logits.argmax(dim=-1)

def compute_metrics(eval_preds):
    # 这个metric其实就是正确率
    metric = evaluate.load("accuracy.py")
    preds, labels = eval_preds
    # preds have the same shape as the labels, after the argmax(-1) has been calculated by preprocess_logits_for_metrics but we need to shift the labels
    # (batch_size, num_steps)去掉labels[0]
    labels = labels[:, 1:].reshape(-1)
    # (batch_size, num_steps)去掉labels[-1]
    preds = preds[:, :-1].reshape(-1)
    return metric.compute(predictions=preds, references=labels)

class SavePeftModelCallback(TrainerCallback):

    def on_save(
            self, 
            args: transformers.TrainingArguments, 
            state: transformers.TrainerState, 
            control: transformers.TrainerControl, 
            **kwargs
    ):
        """
        每次只需保存lora模型，不保存预训练模型
        """
        if state.is_world_process_zero:
            print('********************save call back********************')
            checkpoint_folder = os.path.join(args.output_dir, f"{PREFIX_CHECKPOINT_DIR}-{state.global_step}")
            kwargs['model'].save_pretrained(checkpoint_folder)
            pytorch_model_path = os.path.join(checkpoint_folder, "pytorch_model.bin")
            if os.path.exists(pytorch_model_path):
                os.remove(pytorch_model_path)
            return control
        # return super().on_save(args, state, control, **kwargs)
    
    def on_epoch_end(self, args: transformers.TrainingArguments, state: transformers.TrainerState, control: transformers.TrainerControl, **kwargs):
        if state.is_world_process_zero:
            print('********************on epoch end call back********************')
            print(f"Epoch {state.epoch} finish")
        
        return super().on_epoch_end(args, state, control, **kwargs)
    
    def on_step_end(self, args: transformers.TrainingArguments, state: transformers.TrainerState, control: transformers.TrainerControl, **kwargs):
        if state.is_world_process_zero and state.global_step % 10 == 0:
            print('********************on step end call back********************')
            print(f"Step {state.global_step} finish")

        return super().on_step_end(args, state, control, **kwargs)

def train_model(model, last_checkpoint, tokenizer, train_dataset, eval_dataset, training_args, data_args, logger):
    optimizer = get_optimizer(model, training_args)
    trainer = Trainer(
        model=model,
        args=training_args,
        train_dataset=train_dataset,
        eval_dataset=eval_dataset,
        tokenizer=tokenizer,
        optimizers=(optimizer, None),
        data_collator=transformers.DataCollatorForSeq2Seq(
            tokenizer, pad_to_multiple_of=8, return_tensors="pt", padding=True
        ),
        compute_metrics=compute_metrics if training_args.do_eval else None,
        preprocess_logits_for_metrics=preprocess_logits_for_metrics if training_args.do_eval else None,
        callbacks=([SavePeftModelCallback] if isinstance(model, PeftModel) else None)
    )

    if training_args.do_train:
        # 如果设置了 --resume_from_checkpoint(checkpoint的名字), 从该checkpoint继续训练
        # 如果未设置 --overwrite_output_dir, 并且output_dir中有checkpoint，则从最新的checkpoint开始训练
        # 否则，从头训练
        checkpoint = None
        if training_args.resume_from_checkpoint is not None:
            resume_from_checkpoint = training_args.resume_from_checkpoint
            # 预训练模型
            checkpoint_name = os.path.join(resume_from_checkpoint, "pytorch_model.bin")
            if not os.path.exists(checkpoint_name):
                # lora模型
                checkpoint_name = os.path.join(resume_from_checkpoint, "adapter_model.bin")
                resume_from_checkpoint = (False)
            if os.path.exists(checkpoint_name):
                print(f"从checkpoint {checkpoint_name} 继续训练")
                adapters_weights = torch.load(checkpoint_name)
                set_peft_model_state_dict(model, adapters_weights)
            else:
                print(f"没有找到checkpoint {checkpoint_name}")
        elif last_checkpoint is not None:
            checkpoint = last_checkpoint
        
        if torch.__version__ >= "2" and sys.platform != "win32":
            model = torch.compile(model)  # torch.compile 通过 JIT 将 PyTorch 代码编译成优化的内核，使 PyTorch 代码运行得更快
        
        train_result = trainer.train(resume_from_checkpoint=checkpoint)
        trainer.save_model(os.path.join(training_args.output_dir, f"best_lora_model_{int(time.time())}"))

        metrics = train_result.metrics
        max_train_samples = (
            data_args.max_train_samples 
            if data_args.max_train_samples is not None 
            else len(train_dataset)
        )
        metrics['train_samples'] = min(max_train_samples, len(train_dataset))
        trainer.log_metrics("train", metrics)
        trainer.save_metrics("train", metrics)
        trainer.save_state()
    
    if training_args.do_eval:
        logger.info("*** Evaluate ***")
        metrics = trainer.evaluate()
        max_eval_samples = data_args.max_eval_samples if data_args.max_eval_samples is not None else len(eval_dataset)
        metrics["eval_samples"] = min(max_eval_samples, len(eval_dataset))
        try:
            perplexity = math.exp(metrics["eval_loss"])
        except OverflowError:
            perplexity = float("inf")
        metrics["perplexity"] = perplexity

        trainer.log_metrics("eval", metrics)
        trainer.save_metrics("eval", metrics)


        f = open(data_args.test_output_file, "w", encoding="utf-8")
        logger.info("*** Predict ***")
        predictions, label_ids, metrics = trainer.predict(eval_dataset)
        for (pred, label) in zip(predictions, label_ids):
            pred = [predi for predi in pred if predi != -100]
            pred = tokenizer.decode(pred)
            label = [labeli for labeli in label if labeli != -100]
            label = tokenizer.decode(label)
            f.write(f"{pred}\n{label}\n\n")
            f.flush()
        f.write(f"{metrics}")
        f.close()
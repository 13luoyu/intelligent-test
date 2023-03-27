from transformers import AutoTokenizer, EncoderDecoderModel, Seq2SeqTrainer, AutoModelForSeq2SeqLM
import random
from utils.arguments import arg_parser
from utils.data_loader import read_json, DefaultDataset, DataCollatorForSeq2Seq
from utils.training_arguments import get_seq2seq_training_arguments




def train_model(train_datset, model_path, training_args = {}):
    train_data = read_json(train_datset)
    random.shuffle(train_data)

    Mengzi_tokenizer = AutoTokenizer.from_pretrained(model_path)
    # 同时将Bert模型当成编码器和解码器
    Mengzi_model = EncoderDecoderModel.from_encoder_decoder_pretrained(model_path, model_path)
    
    # 设置句子开始的标记、结束的标记
    Mengzi_tokenizer.bos_token = Mengzi_tokenizer.cls_token
    Mengzi_tokenizer.eos_token = Mengzi_tokenizer.sep_token
    Mengzi_model.config.decoder_start_token_id = Mengzi_tokenizer.bos_token_id
    Mengzi_model.config.eos_token_id = Mengzi_tokenizer.eos_token_id
    Mengzi_model.config.pad_token_id = Mengzi_tokenizer.pad_token_id
    Mengzi_model.config.num_beams = 4

    trainset = DefaultDataset(train_data)
    devset = DefaultDataset(train_data)
    collator = DataCollatorForSeq2Seq(Mengzi_tokenizer)

    after_trained_model_path = training_args["output_dir"]



    training_args = get_seq2seq_training_arguments(training_args)
    trainer = Seq2SeqTrainer(tokenizer = Mengzi_tokenizer, model = Mengzi_model, args = training_args, data_collator = collator, train_dataset = trainset, eval_dataset = devset)
    trainer.train()
    trainer.save_model(f"{after_trained_model_path}/best")
    # pred, _, _ = trainer.predict(devset)
    # with open("zz.txt", "w+") as f:
    #     f.write(str(pred))
    #     f.write("\n")
    #     f.write(str(Mengzi_tokenizer.batch_decode(pred, skip_special_tokens=True)))



if __name__ == "__main__":
    training_args = arg_parser()
    train_model("data/seq2seq_train_data.json", "model/mengzi-bert-base-fin", training_args)

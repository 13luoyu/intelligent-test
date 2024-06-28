import gradio as gr
import time
from transformers import AutoTokenizer, AutoModelForCausalLM, TextIteratorStreamer, BitsAndBytesConfig
from threading import Thread
from peft import PeftModel, PeftConfig
import torch
import sys
import pandas
import argparse



# python chat_gradio_lora.py --model_name_or_path ../model/trained/llama2_rule_element_extraction --mode 4bit-lora


def create_gradio_process(model, tokenizer, streamer):
    with gr.Blocks() as window:  # theme: "soft" or "default"
        gr.Markdown("""<h1><center>智能助手</center></h1>""")
        # 聊天框、输入框和状态栏
        chatbot = gr.Chatbot()
        msg = gr.Textbox()
        state = gr.State()
        # 发送命令按钮
        with gr.Row():
            clear = gr.Button("新话题")
            re_generate = gr.Button("重新回答")
            send_bt = gr.Button("发送")
        # 生成参数
        with gr.Accordion("生成参数", open=False):
            slider_max_new_tokens = gr.Slider(minimum=0, maximum=2048, label="max_new_tokens", value=512)
            slider_do_sample = gr.Radio([True, False], label="do_sample", value=False)
            slider_top_k = gr.Slider(minimum=1, maximum=10000, label="top_k", value=50)
            slider_top_p = gr.Slider(minimum=0.5, maximum=1.0, label="top_p", value=1.0)
            slider_temperature = gr.Slider(minimum=0, maximum=5.0, label="temperature", value=1.0)
            slider_repetition_penalty = gr.Slider(minimum=1.0, maximum=5.0, label="repetition_penalty", value=1.0)
            # 上文轮次
            slider_context_times = gr.Slider(minimum=0, maximum=100, label="lookback_rounds", value=0, step=1.0)
        
        def user(user_message, history):
            return "", history + [[user_message, None]]
        
        def bot(history, max_new_tokens, do_sample, top_k, top_p, temperature, repetition_penalty, slider_context_times):
            if pandas.isnull(history[-1][1]) == False:
                history[-1][1] = None
                yield history
            slider_context_times = int(slider_context_times)
            history_true = history[1:-1]
            prompt = ''
            if slider_context_times > 0:
                chat_his = []
                for one_chat in history_true[-slider_context_times:]:
                    s = ""
                    if one_chat[0]:
                        s += "<s>Human: " + one_chat[0].replace('<br>', '\n') + "\n</s>"
                    s += "<s>Assistant: " + one_chat[1].replace('<br>', '\n') + "\n</s>"
                    chat_his.append(s)
                prompt += "\n".join(chat_his)
            prompt += "<s>Human: " + history[-1][0].replace('<br>', '\n') + "\n</s><s>Assistant:"
            input_ids = tokenizer([prompt], return_tensors="pt", add_special_tokens=False).input_ids[:,-max_new_tokens:]
            if torch.cuda.is_available():
                input_ids = input_ids.to('cuda')
            generate_input = {
                "input_ids": input_ids,
                "max_new_tokens": max_new_tokens,
                "do_sample": do_sample,
                "top_k": top_k,
                "top_p": top_p,
                "temperature": temperature,
                "repetition_penalty": repetition_penalty,
                "streamer": streamer,
                "eos_token_id": tokenizer.eos_token_id,
                "bos_token_id": tokenizer.bos_token_id,
                "pad_token_id": tokenizer.pad_token_id
            }
            thread = Thread(target=model.generate, kwargs=generate_input)
            thread.start()
            start_time = time.time()
            bot_message = ''
            print(f"Human: {history[-1][0]}")
            print("Assistant: ", end="", flush=True)
            for new_text in streamer:
                print(new_text, end="", flush=True)
                if len(new_text) == 0:
                    continue
                if new_text != "</s>":
                    bot_message += new_text
                if "Human:" in bot_message:
                    bot_message = bot_message.split("Human:")[0]
                history[-1][1] = bot_message
                yield history
            end_time = time.time()
            print(f"\n生成耗时: {end_time-start_time}, 文字长度: {len(bot_message)}, 字耗时: {(end_time-start_time) / len(bot_message)}")
        
        msg.submit(user, [msg, chatbot], [msg, chatbot], queue=False) \
            .then(bot, [chatbot, slider_max_new_tokens, slider_do_sample, slider_top_k, slider_top_p, slider_temperature, slider_repetition_penalty, slider_context_times], chatbot)
        send_bt.click(user, [msg, chatbot], [msg, chatbot], queue=False) \
            .then(bot, [chatbot, slider_max_new_tokens, slider_do_sample, slider_top_k, slider_top_p, slider_temperature, slider_repetition_penalty, slider_context_times], chatbot)
        re_generate.click(bot, [chatbot, slider_max_new_tokens, slider_do_sample, slider_top_k, slider_top_p, slider_temperature, slider_repetition_penalty, slider_context_times], chatbot)
        clear.click(lambda: [], None, chatbot, queue=False)
    return window

def get_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model_name_or_path", type=str, help='要加载的模型名词或路径')
    parser.add_argument("--mode", type=str, help="加载base model的模式", default="None", choices=["4bit-lora", "8bit-lora", "lora"])
    args = parser.parse_args()
    return args


def chat_gradio_lora():
    args = get_parser()
    tokenizer = AutoTokenizer.from_pretrained(args.model_name_or_path, use_fast=False)
    tokenizer.pad_token = tokenizer.eos_token
    
    if args.mode == "4bit-lora":
        bnb_config = BitsAndBytesConfig(
            load_in_4bit=True,  # 4位量化
            bnb_4bit_use_double_quant=True,  # 此标志用于嵌套量化，其中第一次量化的量化常数再次量化
            bnb_4bit_quant_type="nf4",  # 设置 bnb.nn.Linear4Bit 层中的量化数据类型。选项是 FP4 和 NF4 数据类型，由 fp4 或 nf4 指定。
            bnb_4bit_compute_dtype=torch.bfloat16  # 设置计算类型
        )
        config = PeftConfig.from_pretrained(args.model_name_or_path)
        tokenizer = AutoTokenizer.from_pretrained(config.base_model_name_or_path, use_fast=False)
        tokenizer.pad_token = tokenizer.eos_token
        model = AutoModelForCausalLM.from_pretrained(config.base_model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else "auto", torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True, quantization_config=bnb_config)
        model = PeftModel.from_pretrained(model, args.model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else "auto")
        model.eval()
        # from auto_gptq import AutoGPTQForCausalLM
        # model = AutoGPTQForCausalLM.from_quantized(args.model_name_or_path,low_cpu_mem_usage=True, device="cuda:0", use_triton=False,inject_fused_attention=False,inject_fused_mlp=False)
    elif args.mode == "8bit-lora":
        config = PeftConfig.from_pretrained(args.model_name_or_path)
        tokenizer = AutoTokenizer.from_pretrained(config.base_model_name_or_path, use_fast=False)
        tokenizer.pad_token = tokenizer.eos_token
        model = AutoModelForCausalLM.from_pretrained(config.base_model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else "auto", torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True, load_in_8bit=True)
        model = PeftModel.from_pretrained(model, args.model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else "auto")
        model.eval()
    elif args.mode == "lora":
        config = PeftConfig.from_pretrained(args.model_name_or_path)
        tokenizer = AutoTokenizer.from_pretrained(config.base_model_name_or_path, use_fast=False)
        tokenizer.pad_token = tokenizer.eos_token
        model = AutoModelForCausalLM.from_pretrained(config.base_model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else "auto", torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True)
        model = PeftModel.from_pretrained(model, args.model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else "auto")
        model.eval()
    else:
        raise ValueError(f"未指定加载base model的模式，必须为 \"4bit-lora\", \"8bit-lora\", \"lora\" 之一")


    streamer = TextIteratorStreamer(tokenizer, skip_prompt=True)
    if torch.__version__ >= "2" and sys.platform != "win32":
        model = torch.compile(model)
    
    window = create_gradio_process(model, tokenizer, streamer)
    window.queue().launch(share=False, debug=True, server_name="0.0.0.0", server_port=7862)


if __name__ == "__main__":
    chat_gradio_lora()
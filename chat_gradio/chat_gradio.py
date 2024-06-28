import gradio as gr
from transformers import AutoTokenizer, AutoModelForCausalLM, TextIteratorStreamer, BitsAndBytesConfig
from threading import Thread
import torch
import time
import sys
import pandas
import argparse


# python chat_gradio.py --model_name_or_path ...


def create_gradio_process(model, tokenizer, streamer):
    with gr.Blocks("soft") as window:  # theme: "soft" or "default"
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
            slider_context_times = gr.Slider(minimum=0, maximum=5, label="lookback_rounds", value=0, step=2.0)
        
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
    parser.add_argument("--mode", type=str, help="加载模型的模式", default="None", choices=["base", "8bit-base"])
    args = parser.parse_args()
    return args


def chat_gradio():
    args = get_parser()
    tokenizer = AutoTokenizer.from_pretrained(args.model_name_or_path, use_fast=False, trust_remote_code=True)
    tokenizer.pad_token = tokenizer.eos_token
    
    if args.mode == "8bit-base":
        model = AutoModelForCausalLM.from_pretrained(args.model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else 'auto', torch_dtype=torch.float16, load_in_8bit=True, trust_remote_code=True, use_flash_attention_2=True)
        model.eval()
    elif args.mode == "base":
        model = AutoModelForCausalLM.from_pretrained(args.model_name_or_path, device_map='cuda:0' if torch.cuda.is_available() else 'auto', torch_dtype=torch.float16, trust_remote_code=True, use_flash_attention_2=True)
        model.eval()
    else:
        raise ValueError(f"未指定加载模型的模式 --mode, 必须为 \"base\", \"8bit-base\" 之一")
    
    streamer = TextIteratorStreamer(tokenizer, skip_prompt=True)
    if torch.__version__ >= "2" and sys.platform != "win32":
        model = torch.compile(model)
    
    window = create_gradio_process(model, tokenizer, streamer)
    window.queue().launch(share=False, debug=True, server_name="0.0.0.0", server_port=7861)




if __name__ == "__main__":
    chat_gradio()
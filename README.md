# Intelligent Test 智能测试

## 项目结构

> - **data/**  存放数据的目录
> - **examples/**  存放使用mengzi h5模型进行微调的示例
>   - *example.py*  微调的代码
>   - *Mengzi_summary.ipynb*  微调的jupyter文件
> - **ir/**  信息抽取baseline模型的训练和测试代码
>   - *information_retrieval.py*  训练和测试的代码
>   - *run_finbert.sh*  使用不同超参数调用information_retrieval.py的脚本，使用FinBERT模型
>   - *run_mengzi.sh*  使用不同的超参数调用information_retrieval.py的脚本，使用Mengzi-bert-base-fin与训练模型
> - **log/**  日志目录
>   - *finbert/*  存放ir/目录下的文件训练FinBERT模型的日志
>   - *mengzi/*  存放ir/目录下的文件训练Mengzi模型的日志
>   - *ours/*  存放ours/目录下的文件训练模型的日志
> - **model/**  存储预训练模型和训练好的模型的目录，这里的模型需要自行下载，包含[*mengzi-bert-base-fin*](https://github.com/Langboat/Mengzi), [*FinBERT*](https://github.com/valuesimplex/FinBERT)（FinBERT需改名为bert_FinBERT并将目录下的json配置文件重命名为config.json）等
> - **ours/**  适用于债券文档处理的，基于ir的训练和测试代码
>   - *main.py*  使用ir方式训练和测试代码
>   - *run.sh*  使用不同的超参数和模型调用main.py的脚本
> - **seq2seq/**  直接从自然语言到R0的训练和测试代码
>   - 目前未使用
> - **support/**  用于统计和分析结果，或生成数据的代码
>   - *generate_dict.py*  读取../data/our_data.json文件，生成../data/our_data.dict文件的代码，用于从数据中自动抽取键，生成字典
>   - *statistic.py*  读取../log目录下的测试的日志文件，生成准确率的代码
> - **utils/**  用于数据处理、输入参数处理的代码
>   - arguments.py  输入超参数及其默认值设置代码
>   - data_loader.py  加载数据的代码
>   - training_arguments.py  依据训练参数生成Hugging Face的TrainingArguments类代码




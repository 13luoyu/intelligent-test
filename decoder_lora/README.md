## 训练和预测说明

- 训练方法：4bit量化预训练模型，lora训练
- 预测方法：
    - 预训练模型和lora合并保存，然后加载预测
        - 预训练模型不量化和lora合并保存
            - 不量化加载预测
            - 8bit加载预测
        - 预训练模型8bit量化和lora合并保存
            - 不量化加载预测
            - 8bit加载预测
        - 预训练模型4bit量化和lora合并保存
            - 不量化加载预测
            - 8bit加载预测
    - 预训练模型和lora在运行时动态合并并预测
        - 预训练模型不量化和lora动态合并并预测
        - 预训练模型8bit量化和lora动态合并并预测
        - 预训练模型4bit量化和lora动态合并并预测
from transformers import PretrainedConfig, PreTrainedModel
from train.BertModel import xavier_init_weights, BertModel



class HFConfig_TC(PretrainedConfig):
    model_type = 'bert'
    def __init__(self, vocab_size = 10000, num_hiddens = 768, norm_shape = [768], ffn_num_input = 768, ffn_num_hiddens = 3072, num_heads = 4, num_layers = 12, dropout = 0.1, max_len=512, key_size=768, query_size=768, value_size=768, use_bias=True, **kwargs):
        super().__init__(**kwargs)
        self.vocab_size = vocab_size
        self.num_hiddens = num_hiddens
        self.norm_shape = norm_shape
        self.ffn_num_input = ffn_num_input
        self.ffn_num_hiddens = ffn_num_hiddens
        self.num_heads = num_heads
        self.num_layers = num_layers
        self.dropout = dropout
        self.max_len = max_len
        self.key_size = key_size
        self.query_size = query_size
        self.value_size = value_size
        self.use_bias = use_bias

        

class HFModel_TC(PreTrainedModel):
    def __init__(self, config):
        super().__init__(config)
        self.config = config
        self.model = BertModel(self.config.vocab_size, self.config.num_hiddens, self.config.norm_shape, self.config.ffn_num_input, self.config.ffn_num_hiddens, self.config.num_heads, self.config.num_layers, self.config.dropout, self.config.max_len, self.config.key_size, self.config.query_size, self.config.value_size, self.config.use_bias)
    def forward(self, input):
        return self.model(input)



def generate_model():
    config = HFConfig_TC(21128, 768, [768], 768, 3072, 4, 12, 0.1, 512)
    model = HFModel_TC(config)
    model.apply(xavier_init_weights)
    model.eval()
    model.save_pretrained("./model")

generate_model()
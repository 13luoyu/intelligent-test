import math
import torch
from transformers import PretrainedConfig, PreTrainedModel
from d2l import torch as d2l




class BertEmbeddings(torch.nn.Module):

    def __init__(self, vocab_size, num_hiddens, max_len, norm_shape, dropout, **kwargs):
        super(BertEmbeddings, self).__init__(**kwargs)
        self.add_module("word_embeddings", torch.nn.Embedding(vocab_size, num_hiddens))
        self.add_module("position_embeddings", torch.nn.Embedding(max_len, num_hiddens))
        self.add_module("token_type_embeddings", torch.nn.Embedding(2, num_hiddens))
        self.add_module("LayerNorm", torch.nn.LayerNorm(norm_shape, eps=1e-12))
        self.add_module("dropout", torch.nn.Dropout(dropout))
    
    def forward(self, tokens, segments):
        # X: (batch_size, num_steps, num_hiddens)
        X = self.word_embeddings(tokens) + self.token_type_embeddings(segments)
        X = X + self.position_embeddings.weight[:X.shape[1], :]
        X = self.LayerNorm(X)  # 对num_hiddens维度进行层归一化
        X = self.dropout(X)
        return X


def sequence_mask(X, valid_len, value=0):
    """Mask irrelevant entries in sequences"""
    # X: (batch_size*num_heads*queries size, keys size)
    maxlen = X.size(1)
    # (1, keys size) < (batch_size*num_heads*query_size, 1)
    mask = torch.arange((maxlen), dtype=torch.float32,
                        device=X.device)[None, :] < valid_len[:, None]
    # mask.shape = (batch_size*num_heads*query_size, keys size)
    # ~mask 取反
    X[~mask] = value
    return X

def masked_softmax(X, valid_lens):
    """Perform softmax operation by masking elements on the last axis."""
    # `X`: 3D tensor, `valid_lens`: 1D or 2D tensor
    if valid_lens is None:
        return torch.nn.functional.softmax(X, dim=-1)
    else:
        # X: (batch_size*num_heads, queries size, keys size)
        shape = X.shape
        if valid_lens.dim() == 1:
            valid_lens = torch.repeat_interleave(valid_lens, shape[1])
        else:
            valid_lens = valid_lens.reshape(-1)
        X = sequence_mask(X.reshape(-1, shape[-1]), valid_lens,
                              value=-1e6)
        # X: (batch_size*num_heads*queries size, keys size)
        # 返回值: (batch_size*num_heads, queries size, key_size)
        return torch.nn.functional.softmax(X.reshape(shape), dim=-1)

class DotProductAttention(torch.nn.Module):
    def __init__(self, dropout, **kwargs):
        super(DotProductAttention, self).__init__(**kwargs)
        self.dropout = torch.nn.Dropout(dropout)
    
    def forward(self, queries, keys, values, valid_lens=None):
        # Shape of `queries`: (`batch_size*num_heads`, no. of queries, `d`)
        # Shape of `keys`: (`batch_size*num_heads`, no. of key-value pairs, `d`)
        # Shape of `values`: (`batch_size*num_heads`, no. of key-value pairs, value dimension)
        # Shape of `valid_lens`: (`batch_size*num_heads`,)
        d = queries.shape[-1]
        # scores: (batch_size*num_heads, queries size, keys size)
        scores = torch.bmm(queries, keys.transpose(1,2)) / math.sqrt(d)
        self.attention_weights = masked_softmax(scores, valid_lens)  # (batch_size*num_heads, queries size, key_size)
        # 返回值: (batch_size*num_heads, queries size, value dimension)
        return torch.bmm(self.dropout(self.attention_weights), values)

def transpose_qkv(X, num_heads):
    X = X.reshape(X.shape[0], X.shape[1], num_heads, -1)
    X = X.permute(0, 2, 1, 3)
    return X.reshape(-1, X.shape[2], X.shape[3])

def transpose_output(X, num_heads):
    X = X.reshape(-1, num_heads, X.shape[1], X.shape[2])
    X = X.permute(0, 2, 1, 3)
    return X.reshape(X.shape[0], X.shape[1], -1)

class BertSelfAttention(torch.nn.Module):
    def __init__(self, key_size, query_size, value_size, num_hiddens, dropout, num_heads, use_bias, **kwargs):
        super(BertSelfAttention, self).__init__(**kwargs)
        self.attention = DotProductAttention(dropout)
        self.query = torch.nn.Linear(query_size, num_hiddens, bias=use_bias)
        self.key = torch.nn.Linear(key_size, num_hiddens, bias=use_bias)
        self.value = torch.nn.Linear(value_size, num_hiddens, bias=use_bias)
        self.num_heads = num_heads
    def forward(self, queries, keys, values, valid_lens):
        # queries, keys, values: (batch_size*num_heads, num_steps, num_hiddens/num_heads)
        queries = transpose_qkv(self.query(queries), self.num_heads)
        keys = transpose_qkv(self.key(keys), self.num_heads)
        values = transpose_qkv(self.value(values), self.num_heads)
        if valid_lens is not None:
            # valid_lens: (batch_size*num_heads)
            valid_lens = torch.repeat_interleave(valid_lens, repeats=self.num_heads, dim=0)
        # output: (batch_size*num_heads, queries size, num_hiddens/num_heads)
        output = self.attention(queries, keys, values, valid_lens)
        output_concat = transpose_output(output, self.num_heads)
        # output_concat: (batch_size, queries size, num_hiddens)
        return output_concat

class BertLayer(torch.nn.Module):

    def __init__(self, key_size, query_size, value_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, dropout, use_bias=True, **kwargs):
        super(BertLayer, self).__init__(**kwargs)
        self.self = BertSelfAttention(key_size, query_size, value_size, num_hiddens, dropout, num_heads, use_bias)
        self.attention_output = torch.nn.Sequential()
        self.attention_output.add_module('dense', torch.nn.Linear(num_hiddens, num_hiddens, use_bias))
        self.attention_output.add_module('LayerNorm', torch.nn.LayerNorm(norm_shape, 1e-12))
        self.attention_output.add_module('dropout', torch.nn.Dropout(dropout))

        self.intermediate = torch.nn.Sequential()
        self.intermediate.add_module('dense', torch.nn.Linear(ffn_num_input, ffn_num_hiddens, use_bias))
        self.intermediate.add_module('intermediate_act_fn', torch.nn.GELU())

        self.output = torch.nn.Sequential()
        self.output.add_module('dense', torch.nn.Linear(ffn_num_hiddens, num_hiddens, use_bias))
        self.output.add_module('LayerNorm', torch.nn.LayerNorm(norm_shape, 1e-12))
        self.output.add_module('dropout', torch.nn.Dropout(dropout))

    def forward(self, X, valid_lens):
        # X: (batch_size, num_steps, num_hiddens)
        X = self.self(X, X, X, valid_lens)
        X = self.attention_output(X)
        X = self.intermediate(X)
        X = self.output(X)
        # X: (batch_size, num_steps, num_hiddens)
        return X



class BertEncoder(torch.nn.Module):

    def __init__(self, num_layers, key_size, query_size, value_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, dropout, use_bias=True, **kwargs):
        super(BertEncoder, self).__init__(**kwargs)
        self.layer = torch.nn.ModuleList()
        for i in range(num_layers):
            self.layer.add_module(f"{i}", BertLayer(key_size, query_size, value_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, dropout, use_bias))
    
    def forward(self, X, valid_lens):
        # X: (batch_size, num_steps, num_hiddens)
        for l in self.layer:
            X = l(X, valid_lens)
        return X

class BertPooler(torch.nn.Module):
    def __init__(self, num_hiddens, use_bias, **kwargs):
        super(BertPooler, self).__init__(**kwargs)
        self.dense = torch.nn.Linear(num_hiddens, num_hiddens, use_bias)
        self.activation = torch.nn.Tanh()
    def forward(self, X):
        Y = self.activation(self.dense(X))
        return Y

class BertModel(torch.nn.Module):
    def __init__(self, vocab_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, num_layers, dropout, max_len=1000, key_size=768, query_size=768, value_size=768, use_bias=True, **kwargs):
        super(BertModel, self).__init__(**kwargs)
        self.embeddings = BertEmbeddings(vocab_size, num_hiddens, max_len, norm_shape, dropout)
        self.encoder = BertEncoder(num_layers, key_size, query_size, value_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, dropout, use_bias)
        self.pooler = BertPooler(num_hiddens, use_bias)

    def forward(self, tokens, segments, valid_lens):
        X = self.embeddings(tokens, segments)
        X = self.encoder(X, valid_lens)
        X = self.pooler(X)
        return X


def xavier_init_weights(m):
    if type(m) == torch.nn.Linear or type(m) == torch.nn.Embedding:
        torch.nn.init.xavier_uniform_(m.weight)

def test_bert_model():
    net = BertModel(21128, 768, [768], 768, 3072, 4, 12, 0.1, 512)
    tokens = torch.randint(0, 21128, (2, 8))  # (batch_size, num_steps)
    segments = torch.tensor([[0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1]])
    print(net(tokens, segments, torch.tensor([4,3])).shape)
    print(net)











class BertModelForTC(torch.nn.Module):
    def __init__(self, vocab_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, num_layers, dropout, max_len=1000, key_size=768, query_size=768, value_size=768, use_bias=True, num_labels=2):
        super().__init__()
        self.bert = BertModel(vocab_size, num_hiddens, norm_shape, ffn_num_input, ffn_num_hiddens, num_heads, num_layers, dropout, max_len, key_size, query_size, value_size, use_bias)
        self.bert_embedding = self.bert.embeddings
        self.bert_encoder = self.bert.encoder
        self.fnn = torch.nn.Sequential(
            torch.nn.Linear(num_hiddens, num_hiddens),
            torch.nn.ReLU(),
            torch.nn.Linear(num_hiddens, num_labels)
        )
    def forward(self, tokens, segments, valid_lens):
        X = self.bert_embedding(tokens, segments)
        X = self.bert_encoder(X, valid_lens)
        X = self.fnn(X)
        return X


def test_bert_tc_model():
    net = BertModelForTC(21128, 768, [768], 768, 3072, 4, 12, 0.1, 512, num_labels=37)
    tokens = torch.randint(0, 21128, (2, 8))  # (batch_size, num_steps)
    segments = torch.tensor([[0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1]])
    print(net(tokens, segments, torch.tensor([4,3])).shape)
    print(net)





if __name__ == "__main__":
    test_bert_model()
    test_bert_tc_model()
import json
import torch
import numpy as np
import os

class Vocab:
    def __init__(self, vocab_file):
        vocab_lines = open(vocab_file, "r", encoding="utf-8").readlines()
        self.token_to_idx = {token.split("\t")[-1].strip(): idx for idx, token in enumerate(vocab_lines)}
        self.idx_to_token = [token.split("\t")[-1].strip() for token in vocab_lines]
    
    def __len__(self):
        return len(self.idx_to_token)
    
    def __getitem__(self, tokens):
        if not isinstance(tokens, (list, tuple)):
            return self.token_to_idx.get(tokens, self.token_to_idx.get("[UNK]"))
        else:
            return [self.__getitem__(token) for token in tokens]
    
    def to_tokens(self, indices):
        if not isinstance(indices, (list, tuple, np.ndarray)):
            return self.idx_to_token[indices] if indices < self.__len__() else "[UNK]"
        else:
            return [self.idx_to_token[index] if index < self.__len__() else "[UNK]" for index in indices]


class TC_Dataset(torch.utils.data.Dataset):
    def __init__(self, text_vocab, label_vocab, datas, max_len, is_train=True):
        self.text_vocab = text_vocab
        self.label_vocab = label_vocab
        self.max_len = max_len
        self.X, self.segments, self.valid_lens, self.Y = [], [], [], []
        for data in datas:
            tokens = list(data['text'])
            if is_train:
                labels = data['label'].split(" ")
                if len(tokens) > max_len - 2:
                    pad_tokens = ['[CLS]'] + tokens[:max_len-2] + ['[SEP]']
                    pad_labels = ['O'] + labels[:max_len-2] + ['O']
                    valid_len = max_len
                else:
                    pad_tokens = ['[CLS]'] + tokens + ['[SEP]'] + ['[PAD]'] * (max_len - len(tokens) - 2)
                    pad_labels = ['O'] + labels + ['O'] * (max_len - len(tokens) - 1)
                    valid_len = len(tokens) + 2
                self.X.append(torch.tensor(self.text_vocab[pad_tokens], dtype=torch.long))
                self.segments.append(torch.ones((max_len), dtype=torch.long))
                self.valid_lens.append(torch.tensor(valid_len, dtype=torch.long))
                self.Y.append(torch.tensor(self.label_vocab[pad_labels], dtype=torch.long))
            else:
                if len(tokens) > max_len - 2:
                    pad_tokens = ['[CLS]'] + tokens[:max_len-2] + ['[SEP]']
                    valid_len = max_len
                else:
                    pad_tokens = ['[CLS]'] + tokens + ['[SEP]'] + ['[PAD]'] * (max_len - len(tokens) - 2)
                    valid_len = len(tokens) + 2
                self.X.append(torch.tensor(self.text_vocab[pad_tokens], dtype=torch.long))
                self.segments.append(torch.ones((max_len), dtype=torch.long))
                self.valid_lens.append(torch.tensor(valid_len, dtype=torch.long))

    def __getitem__(self, idx):
        if(len(self.Y) != 0):
            return (self.X[idx], self.segments[idx], self.valid_lens[idx], self.Y[idx])
        else:
            return (self.X[idx], self.segments[idx], self.valid_lens[idx])

    def __len__(self):
        return len(self.X)

def load_data_tc(batch_size, max_len):
    train_data_dir = "../data/tc_train_data_all_full.json"
    text_vocab = Vocab("vocab.txt")
    label_vocab = Vocab("../data/tc_data.dict")
    train_datas = json.load(open(train_data_dir, "r", encoding="utf-8"))
    train_set = TC_Dataset(text_vocab, label_vocab, train_datas, max_len, is_train=True)
    train_iter = torch.utils.data.DataLoader(train_set, batch_size, shuffle=True)
    test_data_dir = "../data/rules.json"
    test_datas = json.load(open(test_data_dir, "r", encoding="utf-8"))
    test_set = TC_Dataset(text_vocab, label_vocab, test_datas, max_len, is_train=True)
    test_iter = torch.utils.data.DataLoader(test_set, batch_size)
    return train_iter, test_iter, text_vocab, label_vocab

if __name__ == "__main__":
    train_iter, test_iter, text_vocab, label_vocab = load_data_tc(8, 512)
    for x, segment, valid_len, y in train_iter:
        print(x.shape, y.shape)
        print(text_vocab.to_tokens(x[0].detach().numpy()))
        print(label_vocab.to_tokens(y[0].detach().numpy()))
        break
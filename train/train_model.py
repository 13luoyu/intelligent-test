import torch
from train.BertModel import BertModelForTC
from train.data import load_data_tc

def try_gpu(i=0):
    """Return gpu(i) if exists, otherwise return cpu()"""
    if torch.cuda.device_count() >= i + 1:
        return torch.device(f'cuda:{i}')
    return torch.device('cpu')

def train_tc(net, train_iter, test_iter, loss, optimizer, vocab_size, epochs):
    last_test_loss = 1e8
    device = try_gpu()
    net = net.to(device)
    for epoch in range(epochs):
        train_l_sum = 0
        for x, segments, valid_lens, y in train_iter:
            x, segments, valid_lens, y = x.to(device), segments.to(device), valid_lens.to(device), y.to(device)
            optimizer.zero_grad()
            y_hat = net(x, segments, valid_lens)
            l = loss(y_hat.reshape(-1, vocab_size), y.reshape(-1))
            l.sum().backward()
            optimizer.step()
            train_l_sum += l.sum()
        test_l_sum = 0
        net.eval()
        for x, segments, valid_lens, y in test_iter:
            y_hat = net(x, segments, valid_lens)
            l = loss(y_hat.reshape(-1, vocab_size), y.reshape(-1))
            test_l_sum += l.sum()
        print(f"epoch {epoch}, 'train loss': {train_l_sum}, test loss: {test_l_sum}")
        if test_l_sum < last_test_loss:
            last_test_loss = test_l_sum
            torch.save(net, "trained_model.pth")
        net.train()



def train_tc_main(batch_size=8, max_len=512, lr=0.01, epochs=20):
    train_iter, test_iter, text_vocab, label_vocab = load_data_tc(batch_size, max_len)
    label_vocab_size = len(label_vocab)
    net = BertModelForTC(21128, 768, [768], 768, 3072, 4, 12, 0.1, 512, num_labels=label_vocab_size)
    loss = torch.nn.CrossEntropyLoss()
    optimizer = torch.optim.Adam(net.parameters(), lr=lr)
    train_tc(net, train_iter, test_iter, loss, optimizer, label_vocab_size, epochs)



train_tc_main()
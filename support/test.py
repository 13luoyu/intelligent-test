import jieba
def eda(sentence, label, alpha_sr=0.1, alpha_ri=0.1, alpha_rs=0.1, p_rd=0.1, num_aug=9):
    seg_list = jieba.cut(sentence)
    seg_list = " ".join(seg_list)
    words = list(seg_list.split())
    # 需要依据标注修正分词 TODO
    i = 0
    last = ""
    last_word = ""
    label = label.split(" ")
    new_words = []
    for word in words:
        for index, alpha in enumerate(word):
            l = label[i]
            if i == 0:
                last = l
                i += 1
                last_word += alpha
                continue
            # 只需要处理2种情况，1是在词word的中间断开，2是连接两个word
            if l != last:  # B->I, B->O, O->B, I->O, I->B (O->I不存在)
                if last[0] == "B" and l[0] == "I" and last[2:] == l[2:]:  # B->I
                    # 同标签
                    last = l
                    i += 1
                    last_word += alpha
                else:
                    # 换标签
                    if index > 0:  # 情况1
                        new_words.append(last_word)
                        last_word = ""
                    last_word += alpha
                    last = l
                    i += 1
            else:  # I->I, O->O, B->B
                if last[0] == "B" and l[0] == "B":
                    # 换标签
                    if index > 0:  # 情况1
                        new_words.append(last_word)
                        last_word = ""
                    last_word += alpha
                    last = l
                    i += 1
                else:
                    # 同标签
                    last = l
                    i += 1
                    last_word += alpha
        if (i == len(label) - 1) or (i < len(label)-1 and (label[i][0] == "O" or label[i][0] == "B")):  # 分词正确
            new_words.append(last_word)
            last_word = ""
            ...
    print(new_words)
    exit(0)


print(eda(sentence="除本所另有规定外，本所对不同交易方式下的债券交易时间安排如下：(一)采用匹配成交方式的，每个交易日的9:15至9:25为开盘集合匹配时间，9:30至11:30、13:00至15:30为连续匹配时间；(二)采用点击成交、询价成交和协商成交方式的，交易时间为每个交易日的9:00至11:30、13:00至20:00；(三)采用竞买成交方式的，每个交易日的9:00至10:00为卖方提交竞买发起申报时间，10:00至11:30为应价方提交应价申报时间。交易时间内因故停市，交易时间不作顺延。根据市场发展需要，本所可以调整债券交易时间。", label="O B-系统 I-系统 O O O O O O B-系统 I-系统 O O O O O O O O O B-交易品种 I-交易品种 O O O O O O O O O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O O O O O O B-交易方式 I-交易方式 I-交易方式 I-交易方式 O O O O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 I-时间 O B-key I-key I-key I-key I-key I-key I-key I-key I-key I-key I-key O B-时间 I-时间 I-时间 I-时间 I-时间 O O B-状态 I-状态 O O O O O B-结果 I-结果 I-结果 I-结果 O O O O O O O O O O B-系统 I-系统 B-结果 I-结果 B-操作 I-操作 B-操作部分 I-操作部分 I-操作部分 I-操作部分 I-操作部分 I-操作部分 O"))
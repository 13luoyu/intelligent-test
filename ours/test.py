import hanlp

def deal_with_event_precond(event):
    HanLP = hanlp.load(hanlp.pretrained.mtl.CLOSE_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_SMALL_ZH)
    pos= HanLP(event,tasks='pos')

    tok = pos["tok/fine"]
    ctb = pos["pos/ctb"]

    keys, values = [], []
    n, v = "", ""
    last = ""
    for i, c in enumerate(ctb):
        t = tok[i]
        if c == "VV":
            if last == "VV":
                v += t
                continue
            elif last == "NN":
                if n == "本所":
                    keys.append("系统")
                elif n == "会员" or n == "对手方":
                    keys.append("操作人")
                else:
                    keys.append("操作部分")
                values.append(n)
                n = ""
            v += t
        elif c == "NN":
            if last == "DT":
                n += tok[i-1]
            if last == "NN":
                n += t
                continue
            elif last == "VV":
                keys.append("操作")
                values.append(v)
                v = ""
            n += t
        elif c != last:
            if v != "":
                if c != "DEC":
                    keys.append("操作")
                    values.append(v)
                v = ""
            if n != "":
                if n == "本所":
                    keys.append("系统")
                elif n == "会员" or n == "对手方":
                    keys.append("操作人")
                else:
                    keys.append("操作部分")
                values.append(n)
                n = ""
        last = c
    if n != "":
        if n == "本所":
            keys.append("系统")
        elif n == "会员" or n == "对手方":
            keys.append("操作人")
        else:
            keys.append("操作部分")
        values.append(n)
    if v != "":
        keys.append("操作")
        values.append(v)
    return keys, values


texts = ["收到意向申报",
"委托会员申报",
"委托指令被撤销和失效",
"确认后",
"当日提交",
"设置的显示数量完全成交后",  #
"发出报价后",
"询价请求被撤销后",
"申请并经本所认可后",  #
"经前述两笔交易的对手方分别确认后",
"继续交易"]
for content in texts:
    print(deal_with_event_precond(content))
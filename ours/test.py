# import hanlp

# # print(hanlp.pretrained.mtl.ALL)

# HanLP = hanlp.load(hanlp.pretrained.mtl.OPEN_TOK_POS_NER_SRL_DEP_SDP_CON_ELECTRA_BASE_ZH)

# doc = HanLP("报价方发出报价后，未成交部分，可以修改价格和数量等报价要素。", tasks="srl")
# srl = doc["srl"]
# print(srl)
# doc.pretty_print()

# doc = HanLP("在应价申报时间内，债券投资者可以作为应价方提交应价申报。", tasks="srl")
# srl = doc["srl"]
# print(srl)
# doc.pretty_print()


# doc = HanLP("经纪客户委托会员申报并达成债券交易的，应当及时向会员交付相应的债券或者资金。", tasks="srl")
# srl = doc["srl"]
# print(srl)
# doc.pretty_print()


# doc = HanLP("收到意向申报的债券投资者可以通过询价成交、协商成交等方式与意向申报发出方达成交易。", tasks="srl")
# srl = doc["srl"]
# print(srl)
# doc.pretty_print()


import json
file = json.load(open("rules_深圳证券交易所债券交易规则.json", "r", encoding="utf-8"))
for r in file:
    if len(r["text"]) != len(r["label"].split(" ")):
        print(r)
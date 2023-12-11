from flask import Flask, request, Response, jsonify
from flask_cors import CORS
import json
from ours.process_nl_to_sci import nl_to_sci
from ours.process_sci_to_sco import sequence_classification
from ours.process_sco_to_tci import sco_to_tci
from ours.process_tci_to_tco import token_classification
from ours.process_tco_to_r1 import to_r1
from ours.process_r1_to_r2 import preprocess, compose_rules_r1_r2
from ours.process_r2_to_r3 import compose_rules_r2_r3
from ours.process_r3_to_testcase import testcase
from ours.process_testcase_to_outputs import generate_dicts
from ours.process_knowledge import process_knowledge
from ours.consistency_checking import consistency_checking
from ours.main import add_defines
from transfer import mydsl_to_rules, rules_to_json_and_mydsl
import time
from hashlib import md5
import wget
import os
import traceback

# nohup python interface.py >../log/run.log &

sc_model_path = "../model/ours/best_1690658708"
tc_model_path = "../model/ours/best_1696264421"
knowledge_file = '../data/knowledge.json'
dict_file = '../data/tc_data.dict'

app = Flask(__name__)
CORS(app, supports_credentials=True)
# 上传目录
app.config['UPLOAD_FOLDER'] = 'download_files/'
# 支持的文件格式
app.config['ALLOWED_EXTENSIONS'] = {'pdf', 'txt'}
# 接口校验的私钥
app_secret_key = "aitest"
# 接口超时时间，（现在时间-时间戳）超过这个时间的请求失败
app_timeout = 1800000  # 30分钟

log = open("interface.log", "a", encoding="utf-8")
def writelog(s):
    log.write(s)
    log.flush()

# 测试方法
@app.route('/')
def default_page():
    # 对于get方法，获取参数的方法是request.args.get('...')
    # 适用于http://127.0.0.1:5000/?a=b这种情况获取a的值
    # 对于post方法，若参数在body且为form-data，获取参数的方法是request.form.get('...)
    # 若参数在body且为json，方法为request.json(...)
    # 返回JSON数据：return Response(..., mimetype='application/json')
    # 或者：return jsonify(...)
    return '这是一个测试界面，测试成功!'

# 检查签名、时间
def check_timestamp_sign(timestamp, sign):
    if int(time.time() * 1000) - int(timestamp) > app_timeout:  # 超时
        return -2
    if md5(f"{timestamp}{app_secret_key}".encode("utf-8")).hexdigest().upper() != sign:  # 接口校验失败
        return -1
    return 1

def get_timestamp_sign():
    timestamp = str(int(time.time() * 1000))
    sign = md5(f"{timestamp}{app_secret_key}".encode("utf-8")).hexdigest().upper()
    return timestamp, sign

def check_input_params(params):
    lack_msg = "缺少输入参数，请传递"
    if "timeStamp" not in params:
        lack_msg += "时间戳、"
    if "sign" not in params:
        lack_msg += "校验值、"
    lack_msg = lack_msg[:-1]
    if lack_msg != "缺少输入参数，请传":
        return 203, lack_msg
    
    check_ts_result = check_timestamp_sign(params['timeStamp'], params['sign'])
    if check_ts_result == -2:
        return 202, "接口超过使用时间"
    elif check_ts_result == -1:
        return 201, "签名验证失败"

    if "data" not in params:
        lack_msg = "缺少输入参数，请传递接口所需要的输入数据"
        return 203, lack_msg
    return 200, ""

# 判断文件名是否是支持的格式
def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1] in app.config['ALLOWED_EXTENSIONS']

# 上传文件
@app.route('/upload', methods=['POST'])
def upload():
    # TODO: 参数校验
    upload_file = request.files['file']
    if upload_file and allowed_file(upload_file.filename):
        upload_file.save(app.config['UPLOAD_FOLDER'] + upload_file.filename)
        writelog(f"### 访问接口/upload, 上传文件名---{upload_file.filename}---.\n\n")
        return jsonify({"message": "upload success"})
    else:
        writelog(f"### 访问接口/upload, 上传失败.\n\n")
        return jsonify({"message": 'upload failed'})

# 获取输入文件（pdf，txt），或者直接输入一段文字，进行预处理
@app.route('/preprocess', methods=['POST'])
def nl_to_sci_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/preprocess, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)

        fileType, fileData = params['data']['fileType'], params['data']['fileData']
        if fileType == "0":  # 文件
            if ".pdf" in fileData:
                # 下载文件
                filepath = wget.download(fileData, app.config['UPLOAD_FOLDER'])
                filepath = filepath.replace("//", "/")
                os.rename(filepath, filepath.split("?")[0])
                filepath = filepath.split("?")[0]
                filepath = filepath.replace("//", "/")
                # 处理
                sci_data, market_variety = nl_to_sci(filepath)
                timestamp, sign = get_timestamp_sign()
                return_data = {"code": code, "msg": "success", "data": {"sci_data": sci_data, "setting": market_variety}, "timeStamp": timestamp, "sign": sign}
                writelog(f"### 访问接口/preprocess, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
                return jsonify(return_data)
            elif ".txt" in fileData:
                filepath = wget.download(fileData, app.config['UPLOAD_FOLDER'])
                filepath = filepath.replace("//", "/")
                nl_data = open(filepath, 'r', encoding="utf-8").read()
                sci_data, market_variety = nl_to_sci(nl_data=nl_data)
                timestamp, sign = get_timestamp_sign()
                return_data = {"code": code, "msg": "success", "data": {"sci_data": sci_data, "setting": market_variety}, "timeStamp": timestamp, "sign": sign}
                writelog(f"### 访问接口/preprocess, 成todo_fp功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
                return jsonify(return_data)
            else:
                raise ValueError(f"不支持的文件格式：\"{fileData}\"，仅支持处理.pdf/.txt格式的文件")
        elif fileType == "1":  # 数据
            sci_data, market_variety = nl_to_sci(nl_data=fileData)
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": "success", "data": {"sci_data": sci_data, "setting": market_variety}, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/preprocess, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/preprocess, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)


# 规则筛选
@app.route('/rule_filter', methods=['POST'])
def sequence_classification_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/rule_filter, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        sci_data = params["data"]
        sco_data = sequence_classification(sci_data, sc_model_path)
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": sco_data, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/rule_filter, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/rule_filter, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)

# # 更改规则筛选的结果
# @app.route('/rule_filter', methods=['PUT'])
# def sequence_classification_interface_update():
#     sco_data = request.json["data"]
#     json.dump(sco_data, open('rules_cache/sco.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
#     return jsonify({'message': 'update success'})

# 规则元素抽取
@app.route('/rule_element_extraction', methods=['POST'])
def token_classification_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/rule_element_extraction, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        sco_data = params["data"]
        tci_data = sco_to_tci(sco_data)
        knowledge = json.load(open(knowledge_file, "r", encoding="utf-8"))
        tco_data = token_classification(tci_data, knowledge, tc_model_path, dict_file)
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": tco_data, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/rule_element_extraction, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/rule_element_extraction, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)

# # 更改规则元素抽取的结果
# @app.route('/rule_element_extraction', methods=['PUT'])
# def token_classification_interface_update():
#     tco_data = request.json["data"]
#     json.dump(tco_data, open('rules_cache/tco.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
#     return jsonify({'message': 'update success'})

def Rrule_transfer(r):
    defines = {}
    rules = []
    rule = {}
    for line in r.split("\n"):
        line = line.strip()
        if line == "":
            continue
        if line.find("define") == 0:
            defines[line.split(" ")[1]] = line.split(" ")[3]
            continue
        if line.find("rule") == 0:
            if rule != {}:
                rules.append(rule)
                rule = {}
            rule['rule'] = line.split(" ")[1]
        elif line.find("sourceId") == 0:
            rule['sourceId'] = line.split(" ")[1]
        elif line.find("focus:") == 0:
            rule['focus'] = line.split(" ")[1]
        elif line.find("before:") == 0:
            rule['before'] = json.loads((" ".join(line.split(" ")[1:])).replace("'", "\""))
        elif line.find("after:") == 0:
            rule['after'] = json.loads((" ".join(line.split(" ")[1:])).replace("'", "\""))
        else:
            if "text" in rule:
                rule['text'] = rule['text'] + line + "\n"
            else:
                rule['text'] = line + "\n"
    if rule != {}:
        rules.append(rule)
    if defines != {}:
        data = {
            "define": defines,
            "rules": rules
        }
    else:
        data = rules
    return data

def Rrule_back(data):
    s = ""
    if isinstance(data, list):
        rules = data
        defines = {}
    else:
        rules = data['rules']
        defines = data['define']
    for key in list(defines.keys()):
        s += f"define {key} = {defines[key]}\n"
    if len(s)>0:
        s += "\n"
    for rule in rules:
        if "rule" in rule:
            s += f"rule {rule['rule']}\n"
        if "sourceId" in rule:
            s += f"sourceId {rule['sourceId']}\n"
        if "focus" in rule:
            s += f"focus: {rule['focus']}\n"
        if "before" in rule:
            s += f"before: {json.dumps(rule['before'])}\n"
        if "after" in rule:
            s += f"after: {json.dumps(rule['after'])}\n"
        if "text" in rule:
            for t in rule['text'].split("\n"):
                s += f"\t{t}\n"
        s += "\n"
    return s

# 规则合成(R1生成)
@app.route('/rule_assembly', methods=["POST"])
def to_r1_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/rule_assembly, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        tco_data = params["data"]["tco_data"]
        market_variety = params["data"]['setting']
        knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))
        r1_data = to_r1(tco_data, knowledge)
        r1_data = add_defines(r1_data, market_variety)
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": Rrule_transfer(r1_data), "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/rule_assembly, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/rule_assembly, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)

# # 更改规则合成(R1)的结果
# @app.route('/rule_assembly', methods=["PUT"])
# def to_r1_interface_update():
#     r1_data = request.json['data']
#     with open('rules_cache/r1.mydsl', 'w', encoding='utf-8') as f:
#         f.write(r1_data)
#     return jsonify({'message': 'update success'})

# R1->R2
@app.route('/r1_to_r2', methods=['POST'])
def r1_to_r2_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/r1_to_r2, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        r1 = Rrule_back(params['data'])
        defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r1)
        knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))
        rules, vars = preprocess(rules, vars)
        defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
        r2_json = rules_to_json_and_mydsl.r2_to_json(rules)
        r2 = rules_to_json_and_mydsl.to_mydsl(r2_json)

        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": Rrule_transfer(r2), "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/r1_to_r2, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/r1_to_r2, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)

# # 更改R2的结果
# @app.route('/r1_to_r2', methods=["PUT"])
# def r1_to_r2_interface_update():
#     r2_data = request.json['data']
#     with open('rules_cache/r2.mydsl', 'w', encoding='utf-8') as f:
#         f.write(r2_data)
#     return jsonify({'message': 'update success'})

# R2->R3
@app.route('/r2_to_r3', methods=['POST'])
def r2_to_r3_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/r2_to_r3, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        r2 = Rrule_back(params['data'])
        defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r2)
        knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))
        defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
        r3_json = rules_to_json_and_mydsl.r3_to_json(rules)
        r3 = rules_to_json_and_mydsl.to_mydsl(r3_json)

        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": Rrule_transfer(r3), "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/r2_to_r3, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/r2_to_r3, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)

# # 更改R3的结果
# @app.route('/r2_to_r3', methods=["PUT"])
# def r2_to_r3_interface_update():
#     r3_data = request.json['data']
#     with open('rules_cache/r3.mydsl', 'w', encoding='utf-8') as f:
#         f.write(r3_data)
#     return jsonify({'message': 'update success'})

# 测试用例生成
@app.route('/testcase', methods=['POST'])
def test_case_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/testcase, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        r3 = Rrule_back(params['data'])
        defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r3)
        vars = testcase(defines, vars, rules)
        outputs = generate_dicts(vars, rules)

        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": outputs, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/testcase, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/testcase, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)

# # 更改生成的测试用例
# @app.route('/testcase', methods=["PUT"])
# def testcase_interface_update():
#     testcase = request.json['data']
#     json.dump(testcase, open('rules_cache/testcase.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
#     return jsonify({'message': 'update success'})

# 处理领域知识
@app.route('/knowledge', methods=['POST'])
def process_knowledge_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code == 203 and msg == "缺少输入参数，请传递接口所需要的输入数据":
            code = 200
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/knowledge(处理领域知识), 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        data = params['data']
        knowledge, todo_text, _, _ = process_knowledge(data)

        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": {"knowledge":knowledge, "todo_knowledge":todo_text}, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/knowledge(处理领域知识), 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/knowledge(处理领域知识), 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)


# 获取所有领域知识
@app.route('/knowledge_base', methods=['POST'])
def get_all_knowledge_interface():
    params = request.json
    code, msg = check_input_params(params)
    if msg == "缺少输入参数，请传递接口所需要的输入数据":  # 不需要输入参数data
        code = 200
    if code != 200:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/knowledge(获取), 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    
    knowledge = json.load(open('../data/knowledge.json', 'r', encoding='utf-8'))
    timestamp, sign = get_timestamp_sign()
    return_data = {"code": code, "msg": "success", "data": knowledge, "timeStamp": timestamp, "sign": sign}
    writelog(f"### 访问接口/knowledge(获取), 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
    return jsonify(return_data)

# 更新领域知识库
@app.route('/knowledge_base', methods=['PUT'])
def process_knowledge_interface_update():
    params = request.json
    code, msg = check_input_params(params)
    if code != 200:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/knowledge(修改), 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    
    knowledge = request.json['data']
    json.dump(knowledge, open('../data/knowledge.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
    timestamp, sign = get_timestamp_sign()
    return_data = {"code": code, "msg": "success", "data": None, "timeStamp": timestamp, "sign": sign}
    writelog(f"### 访问接口/knowledge(修改), 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
    return jsonify({"message": "update success"})

# 需求一致性检测
@app.route('/consistency_checking', methods=['POST'])
def consistency_checking_interface():
    try:
        params = request.json
        code, msg = check_input_params(params)
        if code != 200:
            timestamp, sign = get_timestamp_sign()
            return_data = {"code": code, "msg": msg, "data": None, "timeStamp": timestamp, "sign": sign}
            writelog(f"### 访问接口/testcase, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
            return jsonify(return_data)
        
        data = params['data']
        new_data = []
        for key in list(data.keys()):
            value = data[key]
            for v in value:
                if "rule" in v:
                    v['rule'] = f"{key}的{v['rule']}"
                else:
                    v['rule'] = f"{key}的"
                new_data.append(v)
        data = Rrule_back(new_data)
        conflict_rules = consistency_checking(data)
        for conflict in conflict_rules:
            rule_ids = conflict['rule_ids']
            # docId, ruleId
            new_rule_ids = []
            for ids in rule_ids:
                docId, ruleId = ids.split("的")[0], ids.split("的")[1]
                new_rule_ids.append({"docId": docId, "ruleId": ruleId})
            conflict['rule_ids'] = new_rule_ids

        timestamp, sign = get_timestamp_sign()
        return_data = {"code": code, "msg": "success", "data": conflict_rules, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/testcase, 成功! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)
    except Exception as e:
        timestamp, sign = get_timestamp_sign()
        return_data = {"code": 204, "msg": traceback.format_exc(), "data": None, "timeStamp": timestamp, "sign": sign}
        writelog(f"### 访问接口/testcase, 错误! 输入数据:\n{params},\n返回数据:\n{return_data}\n\n")
        return jsonify(return_data)










if __name__ == '__main__':
    app.run(host='0.0.0.0', port=9090)
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

sc_model_path = "../model/ours/best_1690658708"
tc_model_path = "../model/ours/best_1698959165"
knowledge_file = '../data/knowledge.json'
dict_file = '../data/tc_data.dict'

app = Flask(__name__)
CORS(app, supports_credentials=True)
# 上传目录
app.config['UPLOAD_FOLDER'] = 'rules_cache/'
# 支持的文件格式
app.config['ALLOWED_EXTENSIONS'] = {'pdf', 'txt'}

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
    return 'welcome!'



# 判断文件名是否是支持的格式
def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1] in app.config['ALLOWED_EXTENSIONS']

# 上传文件
@app.route('/upload', methods=['POST'])
def upload():
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
        if 'file' in params and params['file'] != '' and '.pdf' in params['file']:
            sci_data, market_variety = nl_to_sci(nl_file=app.config['UPLOAD_FOLDER'] + params['file'])
            writelog(f"### 访问接口/preprocess, 处理文件---{params['file']}---, 返回数据:\n{json.dumps(sci_data, ensure_ascii=False, indent=4)}\n交易市场: {market_variety['market']}, 交易品种: {market_variety['variety']}\n\n")
            return jsonify({"data":sci_data, "message":"success", "setting": market_variety})
        elif 'file' in params and params['file'] != '' and '.txt' in params['file']:
            nl_data = open(app.config['UPLOAD_FOLDER'] + params['file'], 'r', encoding="utf-8").read()
            sci_data, market_variety = nl_to_sci(nl_data=nl_data)
            writelog(f"### 访问接口/preprocess, 处理文件---{params['file']}---, 返回数据:\n{json.dumps(sci_data, ensure_ascii=False, indent=4)}\n交易市场: {market_variety['market']}, 交易品种: {market_variety['variety']}\n\n")
            return jsonify({"data":sci_data, "message":"success", "setting": market_variety})
        elif 'input' in params and params['input'] != '':
            sci_data, market_variety = nl_to_sci(nl_data=params['input'])
            writelog(f"### 访问接口/preprocess, 处理输入:\n{params['file']}\n返回数据:\n{json.dumps(sci_data, ensure_ascii=False, indent=4)}\n交易市场: {market_variety['market']}, 交易品种: {market_variety['variety']}\n\n")
            return jsonify({"data":sci_data, "message":"success", "setting": market_variety})
        else:
            writelog(f"### 访问接口/preprocess, 缺少输入参数, 请输入需要转换的句子或文件. \n\n")
            return jsonify({"message":"请输入需要转换的句子或文件"})
    except Exception as e:
        writelog(f"### 访问接口/preprocess, 错误: {e}\n\n")
        return jsonify({"message":e})


# 规则筛选
@app.route('/rule_filter', methods=['POST'])
def sequence_classification_interface():
    try:
        params = request.json
        if "data" in params:
            sci_data = params["data"]
            sco_data = sequence_classification(sci_data, sc_model_path)
            writelog(f"### 访问接口/rule_filter, 输入数据:\n{json.dumps(sci_data, ensure_ascii=False, indent=4)}\n返回数据:\n{json.dumps(sco_data, ensure_ascii=False, indent=4)}\n\n")
            return jsonify({"data":sco_data, "message":"success"})
        else:
            writelog(f"### 访问接口/rule_filter, 缺少输入参数, 请输入要进行规则筛选的句子数据.\n\n")
            return jsonify({"message": "请输入要进行规则筛选的句子数据"})
    except Exception as e:
        writelog(f"### 访问接口/rule_filter, 错误: {e}\n\n")
        return jsonify({"message":e})

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
        if "data" in params:
            sco_data = params["data"]
            tci_data = sco_to_tci(sco_data)
            tco_data = token_classification(tci_data, knowledge_file, tc_model_path, dict_file)
            writelog(f"### 访问接口/rule_element_extraction, 输入数据:\n{json.dumps(sco_data, ensure_ascii=False, indent=4)}\n返回数据:\n{json.dumps(tco_data, ensure_ascii=False, indent=4)}\n\n")
            return jsonify({"data":tco_data, "message":"success"})
        else:
            writelog(f"### 访问接口/rule_element_extraction, 缺少输入参数, 请输入要进行规则元素抽取的句子数据.\n\n")
            return jsonify({"message": "请输入要进行规则元素抽取的句子数据"})
    except Exception as e:
        writelog(f"### 访问接口/rule_element_extraction, 错误: {e}\n\n")
        return jsonify({"message":e})

# # 更改规则元素抽取的结果
# @app.route('/rule_element_extraction', methods=['PUT'])
# def token_classification_interface_update():
#     tco_data = request.json["data"]
#     json.dump(tco_data, open('rules_cache/tco.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
#     return jsonify({'message': 'update success'})

# 规则合成(R1生成)
@app.route('/rule_assembly', methods=["POST"])
def to_r1_interface():
    try:
        params = request.json
        if "data" in params and "setting" in params:
            tco_data = params["data"]
            market_variety = params['setting']
            r1_data = to_r1(tco_data, knowledge_file)
            r1_data = add_defines(r1_data, market_variety)
            writelog(f"### 访问接口/rule_assembly, 输入数据:\n{json.dumps(tco_data, ensure_ascii=False, indent=4)}\n返回数据:\n{r1_data}\n\n")
            return jsonify({"message":"success",'data': r1_data})
        else:
            writelog(f"### 访问接口/rule_assembly, 缺少输入参数, 请输入要进行规则合成的句子数据.\n\n")
            return jsonify({"message": "请输入要进行规则合成的句子数据"})
    except Exception as e:
        writelog(f"### 访问接口/rule_assembly, 错误: {e}\n\n")
        return jsonify({"message":e})

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
        if "data" in params:
            r1 = params['data']
            defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r1)
            knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))

            rules, vars = preprocess(rules, vars)
            defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
            r2_json = rules_to_json_and_mydsl.r2_to_json(rules)
            r2 = rules_to_json_and_mydsl.to_mydsl(r2_json)

            writelog(f"### 访问接口/r1_to_r2, 输入数据:\n{r1}\n返回数据:\n{r2}\n\n")
            return jsonify({'message': 'success', 'data': r2})
        else:
            writelog(f"### 访问接口/r1_to_r2, 缺少输入参数, 请输入要进行理解的规则.\n\n")
            return jsonify({"message": "请输入要进行理解的规则"})
    except Exception as e:
        writelog(f"### 访问接口/r1_to_r2, 错误: {e}\n\n")
        return jsonify({"message":e})

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
        if "data" in params:
            r2 = params['data']
            defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r2)
            knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))

            defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
            r3_json = rules_to_json_and_mydsl.r3_to_json(rules)
            r3 = rules_to_json_and_mydsl.to_mydsl(r3_json)
            writelog(f"### 访问接口/r2_to_r3, 输入数据:\n{r2}\n返回数据:\n{r3}\n\n")
            return jsonify({'message': 'success', 'data': r3})
        else:
            writelog(f"### 访问接口/r2_to_r3, 缺少输入参数, 请输入要进行理解的规则.\n\n")
            return jsonify({"message": "请输入要进行理解的规则"})
    except Exception as e:
        writelog(f"### 访问接口/r2_to_r3, 错误: {e}\n\n")
        return jsonify({"message":e})

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
        if "data" in params:
            r3 = params['data']
            defines, vars, rules = mydsl_to_rules.mydsl_to_rules(r3)
            vars = testcase(defines, vars, rules)
            outputs = generate_dicts(vars, rules)
            writelog(f"### 访问接口/testcase, 输入数据:\n{r3}\n返回数据:\n{outputs}\n\n")
            return jsonify({'message': 'success', 'data': outputs})
        else:
            writelog(f"### 访问接口/testcase, 缺少输入参数, 请输入要生成测试用例的规则.\n\n")
            return jsonify({"message": "请输入要生成测试用例的规则"})
    except Exception as e:
        writelog(f"### 访问接口/testcase, 错误: {e}\n\n")
        return jsonify({"message":e})

# # 更改生成的测试用例
# @app.route('/testcase', methods=["PUT"])
# def testcase_interface_update():
#     testcase = request.json['data']
#     json.dump(testcase, open('rules_cache/testcase.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
#     return jsonify({'message': 'update success'})

# 处理领域知识
@app.route('/knowledge', methods=['POST'])
def process_knowledge_interface():
    process_knowledge('rules_cache/sco.json', 'rules_cache/knowledge.json', 'rules_cache/todo_knowledge.txt')
    knowledge = json.load(open('rules_cache/knowledge.json', 'r', encoding='utf-8'))
    with open('rules_cache/todo_knowledge.txt', 'r', encoding='utf-8') as f:
        s = f.read()
    return jsonify({
        'knowledge': knowledge,
        'todo_knowledge': s,
        'message': 'success'
    })

# 获取所有领域知识
@app.route('/knowledge', methods=['GET'])
def get_all_knowledge_interface():
    knowledge = json.load(open('../data/knowledge.json', 'r', encoding='utf-8'))
    return jsonify({'data':knowledge})

# 手动处理领域知识
@app.route('/knowledge', methods=['PUT'])
def process_knowledge_interface_update():
    knowledge = request.json['data']
    json.dump(knowledge, open('../data/knowledge.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
    return jsonify({"message": "update success"})

# 需求一致性检测
@app.route('/consistency_checking', methods=['POST'])
def consistency_checking_interface():
    try:
        if 'data' in request.json and 'source' in request.json:
            data = request.json['data']
            source = request.json['source']
            conflict_rules = consistency_checking(data, source)
            writelog(f"### 访问接口/consistency_checking, 输入数据:\n{request.json}\n返回数据:\n{conflict_rules}\n\n")
            return jsonify({"message":"success", "conflict_rules": conflict_rules})
        else:
            writelog(f"### 访问接口/consistency_checking, 缺少输入参数, 请输入要检测一致性的规则及其来源.\n\n")
            return jsonify({"message": "请输入要检测一致性的规则及其来源"})
    except Exception as e:
        writelog(f"### 访问接口/consistency_checking, 错误: {e}\n\n")
        return jsonify({"message":e})










if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
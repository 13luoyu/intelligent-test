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
from transfer import mydsl_to_rules, rules_to_json_and_mydsl

sc_model_path = "../model/ours/best_1690658708"
tc_model_path = "../model/ours/best_1690329462"
knowledge_file = '../data/knowledge.json'
dict_file = '../data/tc_data.dict'

app = Flask(__name__)
CORS(app, supports_credentials=True)
# 上传目录
app.config['UPLOAD_FOLDER'] = 'rules_cache/'
# 支持的文件格式
app.config['ALLOWED_EXTENSIONS'] = {'pdf', 'txt'}

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
        return jsonify({"message": "upload success"})
    else:
        return jsonify({"message": 'upload failed'})

# 获取输入文件（pdf，txt），或者直接输入一段文字，进行预处理
@app.route('/preprocess', methods=['POST'])
def nl_to_sci_interface():
    params = request.json
    if 'file' in params and params['file'] != '':
        nl_to_sci(app.config['UPLOAD_FOLDER'] + params['file'], 'rules_cache/sci.json')
        sci_data = json.load(open('rules_cache/sci.json', "r", encoding="utf-8"))
        return jsonify({"data":sci_data, "message":"success"})
    elif 'input' in params and params['input'] != '':
        with open('rules_cache/input.txt', "w", encoding="utf-8") as f:
            f.write(params['input'])
        nl_to_sci('rules_cache/input.txt', 'rules_cache/sci.json')
        sci_data = json.load(open('rules_cache/sci.json', "r", encoding="utf-8"))
        return jsonify({"data":sci_data, "message":"success"})
    else:
        return jsonify({"message":"请输入需要转换的句子或文件"})


# 规则筛选
@app.route('/rule_filter', methods=['POST'])
def sequence_classification_interface():
    sequence_classification('rules_cache/sci.json', 'rules_cache/sco.json', sc_model_path)
    sco_data = json.load(open('rules_cache/sco.json', "r", encoding="utf-8"))
    return jsonify({"data":sco_data, "message":"success"})

# 更改规则筛选的结果
@app.route('/rule_filter', methods=['PUT'])
def sequence_classification_interface_update():
    sco_data = request.json["data"]
    json.dump(sco_data, open('rules_cache/sco.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
    return jsonify({'message': 'update success'})

# 规则元素抽取
@app.route('/rule_element_extraction', methods=['POST'])
def token_classification_interface():
    sco_to_tci('rules_cache/sco.json', 'rules_cache/tci.json')
    token_classification('rules_cache/tci.json', 'rules_cache/tco.json', knowledge_file, tc_model_path, dict_file)
    tco_data = json.load(open('rules_cache/tco.json', 'r', encoding="utf-8"))
    return jsonify({"data":tco_data, "message":"success"})

# 更改规则元素抽取的结果
@app.route('/rule_element_extraction', methods=['PUT'])
def token_classification_interface_update():
    tco_data = request.json["data"]
    json.dump(tco_data, open('rules_cache/tco.json', 'w', encoding='utf-8'), ensure_ascii=False, indent=4)
    return jsonify({'message': 'update success'})

# 规则合成(R1生成)
@app.route('/rule_assembly', methods=["POST"])
def to_r1_interface():
    to_r1('rules_cache/tco.json', 'rules_cache/r1.mydsl', knowledge_file)
    with open('rules_cache/r1.mydsl', 'r', encoding="utf-8") as f:
        s = f.read()
    return jsonify({"message":"success",'data': s})

# 更改规则合成(R1)的结果
@app.route('/rule_assembly', methods=["PUT"])
def to_r1_interface_update():
    r1_data = request.json['data']
    with open('rules_cache/r1.mydsl', 'w', encoding='utf-8') as f:
        f.write(r1_data)
    return jsonify({'message': 'update success'})

# R1->R2
@app.route('/r1_to_r2', methods=['POST'])
def r1_to_r2_interface():
    defines, vars, rules = mydsl_to_rules.read_file('rules_cache/r1.mydsl')
    knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))
    rules, vars = preprocess(rules, vars)
    json.dump(rules, open('rules_cache/r1.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    defines, vars, rules = compose_rules_r1_r2(defines, vars, rules, knowledge)
    json.dump(rules, open('rules_cache/r2.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    r2_json = rules_to_json_and_mydsl.r2_to_json(rules)
    rules_to_json_and_mydsl.to_mydsl(r2_json, 'rules_cache/r2.mydsl')
    with open('rules_cache/r2.mydsl', 'r', encoding="utf-8") as f:
        s = f.read()
    return jsonify({'data': s})

# 更改R2的结果
@app.route('/r1_to_r2', methods=["PUT"])
def r1_to_r2_interface_update():
    r2_data = request.json['data']
    with open('rules_cache/r2.mydsl', 'w', encoding='utf-8') as f:
        f.write(r2_data)
    return jsonify({'message': 'update success'})

# R2->R3
@app.route('/r2_to_r3', methods=['POST'])
def r2_to_r3_interface():
    defines, vars, rules = mydsl_to_rules.read_file('rules_cache/r2.mydsl')
    knowledge = json.load(open(knowledge_file, 'r', encoding="utf-8"))
    defines, vars, rules = compose_rules_r2_r3(defines, vars, rules, knowledge)
    json.dump(rules, open('rules_cache/r3.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    r3_json = rules_to_json_and_mydsl.r3_to_json(rules)
    rules_to_json_and_mydsl.to_mydsl(r3_json, 'rules_cache/r3.mydsl')
    with open('rules_cache/r3.mydsl', 'r', encoding="utf-8") as f:
        s = f.read()
    return jsonify({'data': s})

# 更改R3的结果
@app.route('/r2_to_r3', methods=["PUT"])
def r2_to_r3_interface_update():
    r3_data = request.json['data']
    with open('rules_cache/r3.mydsl', 'w', encoding='utf-8') as f:
        f.write(r3_data)
    return jsonify({'message': 'update success'})

# 测试用例生成
@app.route('/testcase', methods=['POST'])
def test_case_interface():
    defines, vars, rules = mydsl_to_rules.read_file('rules_cache/r3.mydsl')
    vars = testcase(defines, vars, rules)
    outputs = generate_dicts(vars, rules)
    json.dump(outputs, open('rules_cache/testcase.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    return jsonify({"message":"success", "data":outputs})

# 更改生成的测试用例
@app.route('/testcase', methods=["PUT"])
def testcase_interface_update():
    testcase = request.json['data']
    json.dump(testcase, open('rules_cache/testcase.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    return jsonify({'message': 'update success'})

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

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
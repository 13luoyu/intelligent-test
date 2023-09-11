from flask import Flask, request, Response, jsonify
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
from transfer import mydsl_to_rules, rules_to_json_and_mydsl

sc_model_path = "../model/ours/best_1690658708"
tc_model_path = "../model/ours/best_1690329462"
knowledge_file = '../data/knowledge.json'
dict_file = '../data/tc_data.dict'

app = Flask(__name__)
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
        return jsonify("upload success")
    else:
        return jsonify('upload failed')

# 获取输入文件（pdf，txt），或者直接输入一段文字，进行预处理
@app.route('/preprocess', methods=['POST'])
def nl_to_sci_interface():
    params = request.json
    if 'file' in params and params['file'] != '':
        nl_to_sci(app.config['UPLOAD_FOLDER'] + params['file'], 'rules_cache/sci.json')
        sci_data = json.load(open('rules_cache/sci.json', "r", encoding="utf-8"))
        return jsonify(sci_data)
    elif 'input' in params and params['input'] != '':
        with open('rules_cache/input.txt', "w", encoding="utf-8") as f:
            f.write(params['input'])
        nl_to_sci('rules_cache/input.txt', 'rules_cache/sci.json')
        sci_data = json.load(open('rules_cache/sci.json', "r", encoding="utf-8"))
        return jsonify(sci_data)
    else:
        return jsonify("请输入需要转换的句子或文件")


# 规则筛选
@app.route('/rule_filter', methods=['POST'])
def sequence_classification_interface():
    sequence_classification('rules_cache/sci.json', 'rules_cache/sco.json', sc_model_path)
    sco_data = json.load(open('rules_cache/sco.json', "r", encoding="utf-8"))
    return jsonify(sco_data)

# 规则元素抽取
@app.route('/rule_element_extraction', methods=['POST'])
def token_classification_interface():
    sco_to_tci('rules_cache/sco.json', 'rules_cache/tci.json')
    token_classification('rules_cache/tci.json', 'rules_cache/tco.json', knowledge_file, tc_model_path, dict_file)
    tco_data = json.load(open('rules_cache/tco.json', 'r', encoding="utf-8"))
    return jsonify(tco_data)

# 规则合成
@app.route('/rule_assembly', methods=["POST"])
def to_r1_interface():
    to_r1('rules_cache/tco.json', 'rules_cache/r1.mydsl', knowledge_file)
    with open('rules_cache/r1.mydsl', 'r', encoding="utf-8") as f:
        s = f.read()
    return jsonify(s)

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
    return jsonify(s)

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
    return jsonify(s)

# 测试用例生成
@app.route('/testcase', methods=['POST'])
def test_case_interface():
    defines, vars, rules = mydsl_to_rules.read_file('rules_cache/r3.mydsl')
    vars = testcase(defines, vars, rules)
    outputs = generate_dicts(vars, rules)
    json.dump(outputs, open('rules_cache/testcase.json', "w", encoding="utf-8"), ensure_ascii=False, indent=4)
    return jsonify(outputs)


if __name__ == '__main__':
    app.run(host='127.0.0.1', port=5000)
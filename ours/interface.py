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

@app.route('/upload', methods=['POST'])
def upload():
    upload_file = request.files['file']
    if upload_file and allowed_file(upload_file.filename):
        upload_file.save(app.config['UPLOAD_FOLDER'] + upload_file.filename)
        return jsonify("upload success")
    else:
        return jsonify('upload failed')

# 获取输入文件（pdf，txt），或者直接输入一段文字，记录并转换为句分类的输入格式
@app.route('/nl_to_sci', methods=['POST'])
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

# 



if __name__ == '__main__':
    app.run(host='127.0.0.1', port=5000)
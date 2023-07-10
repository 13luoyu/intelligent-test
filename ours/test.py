import requests

from requests.auth import HTTPBasicAuth

def extract_from_text(doc_text,
                      min_doc_text_size= 10,
                      fds_ner_svc_url= 'https://api.factset.com/cognitive/nlp/v1/ner/entities'):
    if (not doc_text or not doc_text.strip() or min_doc_text_size> len(doc_text)):
        return None

    payload = {
        'data':{
            'text': doc_text
        }
    }
    response_json = None
    try:
        resp = requests.post(fds_ner_svc_url, json=payload, auth=HTTPBasicAuth('username-serial', 'api-key'))
        if not resp:
            status_code = resp.status_code if (resp is not None) else -1
            raise ValueError(f'Received unexpected response from service: status_code: {status_code}')
        response_json = resp.json()
    except Exception as ex:
        raise ex

    if (not response_json or not isinstance(response_json, dict)
        or ('errors' in response_json) or ('data' not in response_json)):
        return None
    return response_json['data']['entities']

extract_from_text("")
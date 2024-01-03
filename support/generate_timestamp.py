import time
from hashlib import md5
app_secret_key = "aitest"


def get_timestamp_sign():
    timestamp = str(int(time.time() * 1000))
    sign = md5(f"{timestamp}{app_secret_key}".encode("utf-8")).hexdigest().upper()
    return timestamp, sign

print(get_timestamp_sign())
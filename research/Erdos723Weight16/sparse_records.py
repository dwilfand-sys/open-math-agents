"""Combine checked seed ranges and compress their explicit interior records."""
import argparse
import base64
import json
from pathlib import Path
import zlib


def read_records(path):
    raw=json.loads(path.read_text(encoding='utf8'))
    if raw.get('format')=='zlib+base64-json-v1':
        plain=zlib.decompress(base64.b64decode(raw['data'],validate=True))
        return json.loads(plain)
    return raw


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output',type=Path)
    ap.add_argument('inputs',type=Path,nargs='+')
    ap.add_argument('--seeds',type=int,required=True)
    args=ap.parse_args()
    merged={}
    for path in args.inputs:
        for i,row in read_records(path).items():
            if i in merged and merged[i]!=row:
                raise ValueError(f'inconsistent searches at seed {i}')
            merged[i]=row
    if set(merged)!=set(map(str,range(args.seeds))):
        raise ValueError('incomplete or extra seed range')
    raw=json.dumps({i:merged[str(i)] for i in range(args.seeds)},separators=(',',':')).encode('ascii')
    encoded=base64.b64encode(zlib.compress(raw,9)).decode('ascii')
    args.output.write_bytes((json.dumps({'format':'zlib+base64-json-v1','data':encoded},separators=(',',':'))+'\n').encode('ascii'))
    if read_records(args.output)!=merged:
        raise ValueError('compressed readback differs from the input')

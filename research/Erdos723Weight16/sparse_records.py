"""Combine checked seed ranges and compress their explicit interior records."""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import zlib


def read_records(path):
    raw=json.loads(path.read_text(encoding='utf8'))
    if raw.get('format')=='zlib+base64-json-v1':
        plain=zlib.decompress(base64.b64decode(raw['data'],validate=True))
        return json.loads(plain)
    if raw.get('format')=='sparse-seed-parts-v1':
        out={}
        for part in raw['parts']:
            name=part['file']
            if Path(name).name!=name:
                raise ValueError('part name must be in the same directory')
            child=path.with_name(name)
            if hashlib.sha256(child.read_bytes()).hexdigest()!=part['sha256']:
                raise ValueError(f'incorrect digest for {name}')
            data=read_records(child)
            if not out.keys().isdisjoint(data):
                raise ValueError('overlapping seed parts')
            out.update(data)
        if set(out)!=set(map(str,range(raw['seeds']))):
            raise ValueError('incorrect seed range in parts')
        return out
    return raw


def same_terminal_data(left,right):
    def normalized(row):
        return (row['seed'],row['orbit_size'],sorted(row['inside'],key=lambda v:v['blocks']))
    return normalized(left)==normalized(right)


def compressed_bytes(records):
    raw=json.dumps(records,separators=(',',':')).encode('ascii')
    encoded=base64.b64encode(zlib.compress(raw,9)).decode('ascii')
    return (json.dumps({'format':'zlib+base64-json-v1','data':encoded},separators=(',',':'))+'\n').encode('ascii')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output',type=Path)
    ap.add_argument('inputs',type=Path,nargs='+')
    ap.add_argument('--seeds',type=int,required=True)
    ap.add_argument('--per-part',type=int,help='split records into groups of this many seeds')
    args=ap.parse_args()
    merged={}
    for path in args.inputs:
        for i,row in read_records(path).items():
            if i in merged and not same_terminal_data(merged[i],row):
                raise ValueError(f'inconsistent searches at seed {i}')
            if i not in merged or row.get('nodes_by_depth'):
                merged[i]=row
    if set(merged)!=set(map(str,range(args.seeds))):
        raise ValueError('incomplete or extra seed range')
    if args.per_part is None:
        args.output.write_bytes(compressed_bytes({i:merged[str(i)] for i in range(args.seeds)}))
    else:
        if args.per_part<1:
            ap.error('--per-part must be positive')
        parts=[]
        for start in range(0,args.seeds,args.per_part):
            stop=min(start+args.per_part,args.seeds)
            child=args.output.with_name(f'{args.output.stem}.{start:03d}-{stop-1:03d}.json')
            packed=compressed_bytes({i:merged[str(i)] for i in range(start,stop)})
            child.write_bytes(packed)
            parts.append({'file':child.name,'sha256':hashlib.sha256(packed).hexdigest()})
        manifest={'format':'sparse-seed-parts-v1','seeds':args.seeds,'parts':parts}
        args.output.write_bytes((json.dumps(manifest,indent=2)+'\n').encode('ascii'))
    if read_records(args.output)!=merged:
        raise ValueError('compressed readback differs from the input')

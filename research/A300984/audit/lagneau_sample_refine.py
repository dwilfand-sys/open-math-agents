"""Try alternative representatives for members still missing a squarefreeness certificate."""

from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path

from lagneau_exact_sample import certified, factor_values
from lagneau_prime_sample import SQUARES


def main():
    parser=ArgumentParser()
    parser.add_argument('file')
    parser.add_argument('--seconds',type=float,default=4)
    a=parser.parse_args()
    path=Path(a.file)
    cert=json.loads(path.read_text(encoding='utf8'))
    limit=10**cert['m']
    witnesses=cert['witnesses']
    unknown=[p for p,_,pr in cert['sample'] if not pr and str(p) not in witnesses]
    print('unproven',len(unknown),flush=True)
    cached={int(q):True for q in cert['primality_certificates']}
    pending=[]
    for p in unknown:
        power=p*p
        ps=1+p+power
        n,ts=4*power,7
        possible=[]
        while n<=limit:
            f=ts*ps-3*(p+1)
            if all(f%s for s in SQUARES):
                possible.append((n,f))
            n,ts=n*2,ts*2+1
        if possible:
            pending.append((p,possible[1:]+possible[:1]))
    def check(item):
        p,fu=item
        newcerts={}
        known=cached.copy()
        for n,f in fu:
            fs=factor_values([f],a.seconds).get(f,())
            if fs and len(fs)==len(set(fs)) and all(certified(q,known,newcerts) for q in fs):
                return str(p),[n,f,fs],newcerts
        return str(p),None,{}
    with ThreadPoolExecutor(2) as pool:
        for pos,(p,record,cc) in enumerate(pool.map(check,pending)):
            if record:
                witnesses[p]=record
                cert['primality_certificates'].update(cc)
            if (pos+1)%30==0 or pos+1==len(pending):
                path.write_text(json.dumps(cert,separators=(',',':')),encoding='utf8')
                print('checked',pos+1,'of',len(pending),'certified',len(witnesses),flush=True)


if __name__=='__main__':
    main()

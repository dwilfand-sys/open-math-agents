"""Emit a prefix-encoded finite proof partition for an odd square with k prime factors."""
import gzip
from collections import Counter
from pathlib import Path
import sys

from modular_boxes import character_bounds, extension_bounds, mod_exclusion, normalize, ratio

ROOT=Path(__file__).parent

def put_varint(data,n):
    while n>=128:
        data.append(128|(n&127))
        n//=128
    data.append(n)

def build(k):
    data=bytearray(b"APB1"+bytes([k]))
    stack=[[(3,0,2,False)]*k]
    counts=Counter()
    while stack:
        box=normalize(stack.pop())
        if box is None:
            data.append(0);counts[0]+=1;continue
        box=character_bounds(box)
        if box is None:
            data.append(1);counts[1]+=1;continue
        box=extension_bounds(box)
        if box is None:
            data.append(2);counts[2]+=1;continue
        ln=ld=un=ud=minn=1
        for p,q,e,x in box:
            if q:
                a,b=ratio(q,e)
                ln*=a;ld*=b
            a,b=ratio(p,e);minn*=b
            un*=a if x else p;ud*=b if x else p-1
        if ln>=2*ld:
            data.append(3);counts[3]+=1;continue
        if un*minn+ud<2*ud*minn:
            data.append(4);counts[4]+=1;continue
        if mod_exclusion(box):
            data.append(5);counts[5]+=1;continue
        choices=[]
        for i,(lo,hi,e,exact) in enumerate(box):
            if lo!=hi:
                choices.append((1/(lo-1)-(1/(hi-1) if hi else 0),True,i))
            if not exact:
                choices.append((lo**(-e-1),False,i))
        _,p_split,j=max(choices)
        lo,hi,e,exact=box[j]
        if p_split:
            tag=16+j
            if lo<19 or hi and hi-lo<8:
                cut=lo
            else:
                cut=2*lo*hi//(lo+hi) if hi else 2*lo
                if hi: cut=min(cut,hi-1)
            children=[(lo,cut,e,exact),(cut+1,hi,e,exact)]
        else:
            tag=32+j
            cut=e
            children=[(lo,hi,e,True),(lo,hi,e+2,False)]
        data.append(tag);counts[tag]+=1
        put_varint(data,cut)
        for child in children:
            stack.append(box[:j]+(child,)+box[j+1:])
    filename=ROOT/f"odd_{k}_certificate.gz"
    filename.write_bytes(gzip.compress(data,compresslevel=9,mtime=0))
    print(k,sum(counts.values()),len(data),filename.stat().st_size,sorted(counts.items()),flush=True)

if __name__=="__main__":
    for m in sys.argv[1:]:
        build(int(m))

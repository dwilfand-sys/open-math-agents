"""Independent segmented reconstruction of the full positive-slope counts."""
from argparse import ArgumentParser
from math import isqrt
from pathlib import Path
import json
import numpy as np


def primes(maximum):
    a=bytearray([1])*(maximum+1)
    a[:2]=bytes(2)
    for q in range(2,isqrt(maximum)+1):
        if a[q]:
            a[q*q::q]=bytes((maximum-q*q)//q+1)
    return [i for i in range(2,maximum+1) if a[i]]


def prime_flags(n0,delta,count,trials):
    bits=bytearray([1])*count
    end=n0+delta*(count-1)
    for q,inverse in trials:
        if q*q>end:
            break
        # Solve the progression in offsets from this segment's first value.
        root=(-n0*inverse)%q
        first=max(0,(q*q-n0+delta-1)//delta)
        j=first+(root-first)%q
        if j<count:
            bits[j::q]=bytes((count-1-j)//q+1)
    return np.frombuffer(bits,dtype=np.uint8)


def replay(t):
    slopes,thresholds=t['slopes'],t['smallThresholds']
    D,U,chunk=t['maxDivisor'],t['upper'],t['blockSize']
    polynomials=[(6,1),(12,1)]+[(12*s,2*s-1) for s in slopes]
    qs=primes(isqrt(2*max(slopes)*U))
    trials={m:[(q,pow(m,-1,q)) for q in qs if m%q] for m,c in polynomials}
    allm=1<<len(slopes)
    factors=[[10**15]*allm for _ in thresholds]
    counts=[[0]*allm for _ in thresholds]
    splits=sorted({D//v for v in thresholds}|{U})
    for left,right in zip(splits,splits[1:]):
        start,stop=(left-1)//6+1,(right-1)//6+1
        for base in range(start,stop,64*chunk):
            n=min(stop-base,64*chunk)
            r=prime_flags(6*base+1,6,n,trials[6])
            ordinary=prime_flags(12*base+1,12,n,trials[12])
            eligible=((r!=0)&(ordinary==0))
            signatures=np.zeros(n,dtype=np.uint8)
            for j,(m,c) in enumerate(polynomials[2:]):
                signatures |= prime_flags(m*base+c,m,n,trials[m])<<j
            for pos in range(0,n,chunk):
                end=min(pos+chunk,n)
                segment=signatures[pos:end][eligible[pos:end]]
                hist=np.bincount(segment,minlength=allm).tolist()
                # Directly sum the disjoint signatures intersecting each mask.
                combined=[sum(nh for key,nh in enumerate(hist) if mask&key)
                          for mask in range(allm)]
                bound=6*(base+end-1)+1
                for v,th in enumerate(thresholds):
                    if left<D//th:
                        continue
                    for mask,c in enumerate(combined):
                        counts[v][mask]+=c
                        factors[v][mask]=(factors[v][mask]*bound+bound+c-1)//(bound+c)
    assert counts==t['counts']
    assert factors==[[int(x) for x in row] for row in t['factors']]
    print('Verified counts and multipliers for all',len(thresholds)*allm,
          'threshold/mask pairs through',U)


if __name__=='__main__':
    ap=ArgumentParser()
    ap.add_argument('table',type=Path)
    f=ap.parse_args().table
    replay(json.loads(f.read_text()))

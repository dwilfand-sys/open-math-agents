"""Check every mask and outward factor in a small positive-residue slope table."""
from argparse import ArgumentParser
import json
from math import isqrt
from pathlib import Path


def main():
    ap=ArgumentParser()
    ap.add_argument('table',type=Path)
    t=json.loads(ap.parse_args().table.read_text())
    slopes=t['slopes']
    d,upper,chunk=t['maxDivisor'],t['upper'],t['blockSize']
    cap=2*max(slopes)*upper
    if cap>50_000_000:
        raise ValueError('Use the small fixture for this ordinary integer sieve')
    prime=bytearray([1])*(cap+1)
    prime[:2]=bytes(2)
    for q in range(2,isqrt(cap)+1):
        if prime[q]:
            prime[q*q::q]=bytes((cap-q*q)//q+1)
    splits=sorted({d//s for s in t['smallThresholds']}|{upper})
    for threshold,cs,fs in zip(t['smallThresholds'],t['counts'],t['factors']):
        for mask in range(1<<len(slopes)):
            active=[s for j,s in enumerate(slopes) if mask>>j&1]
            factor=10**15
            total=0
            for left,right in zip(splits,splits[1:]):
                if left < d//threshold:
                    continue
                ks=range((left-1)//6+1,(right-1)//6+1)
                for ix in range(0,len(ks),chunk):
                    numbers=[6*k+1 for k in ks[ix:ix+chunk]]
                    count=sum(bool(prime[r]) and not prime[2*r-1] and
                              any(prime[2*s*r-1] for s in active) for r in numbers)
                    maximum=numbers[-1]
                    factor=(factor*maximum+maximum+count-1)//(maximum+count)
                    total+=count
            assert (total,factor)==(cs[mask],int(fs[mask])),(threshold,mask)
    print('Verified all ordinary integer sieve counts and multipliers:',
          len(t['smallThresholds'])*(1<<len(slopes)),'threshold/mask pairs')


if __name__=='__main__':
    main()

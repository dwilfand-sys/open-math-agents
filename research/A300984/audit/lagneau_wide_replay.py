"""Rebuild the full wide-graph edge counts and Janson moments with NumPy."""
from argparse import ArgumentParser
from math import isqrt
from pathlib import Path
import json
import numpy as np


def odd_prime_bits(maximum):
    lim=isqrt(maximum)
    base=bytearray([1])*(lim+1)
    for p in range(2,isqrt(lim)+1):
        if base[p]:
            base[p*p::p]=bytes((lim-p*p)//p+1)
    primes=[p for p in range(3,lim+1,2) if base[p]]
    oddcount=(maximum+1)//2
    bitset=np.empty((oddcount+7)//8,dtype=np.uint8)
    for idx in range(0,oddcount,2**22):
        size=min(2**22,oddcount-idx)
        lo=2*idx+1
        covered=bytearray([1])*size
        if idx==0: covered[0]=0
        for p in primes:
            if p*p>lo+2*(size-1): break
            first=max(p*p,((lo+p-1)//p)*p)
            if first%2==0: first+=p
            j=(first-lo)//2
            if j<size: covered[j::p]=bytes((size-1-j)//p+1)
        packed=np.packbits(np.frombuffer(covered,dtype=np.uint8),bitorder='little')
        bitset[idx//8:idx//8+len(packed)]=packed
    def isprime(n):
        # Callers use odd positive integers in range.
        i=n//2
        return (bitset[i//8]>>(i%8))&1
    return isprime


def replay(table):
    D,B,S=table['cap'],table['B'],table['precision']
    prime=odd_prime_bits(2*D)
    # Begin at the first odd integer strictly above B.
    possible=np.arange(B+1+B%2,D//(B+1)+1,2,dtype=np.int64)
    vertices=possible[(prime(possible)!=0)&(prime(2*possible-1)==0)]
    del possible
    for row in table['rows']:
        t=row['small']
        v=vertices if not t else vertices[prime(2*t*vertices-1)==0]
        lo=S//v
        hi=(S+v-2)//(v-1)
        sums=np.zeros(len(v),dtype=np.int64)
        squares=np.zeros(len(v),dtype=np.int64)
        edges=0
        first=0
        for i in range(int(v.searchsorted(isqrt(D),side='right'))):
            r=int(v[i])
            ub=int(v.searchsorted(D//r,side='right'))
            xs=v[i+1:ub]
            qualifies=prime(2*r*xs-1)!=0
            if t:
                cut=int(xs.searchsorted(D//(r*t),side='right'))
                qualifies[:cut]|=prime(2*t*r*xs[:cut]-1)!=0
            hits=np.flatnonzero(qualifies)+i+1
            edges+=int(hits.size)
            first+=int(lo[i])*int(lo[hits].sum())
            hh=hi[hits]
            sums[i]+=hh.sum()
            squares[i]+=(hh*hh).sum()
            sums[hits]+=hi[i]
            squares[hits]+=hi[i]*hi[i]
        stars=sum(int(w)*(int(h)**2-int(h2)) for w,h,h2 in zip(hi,sums,squares))
        assert (len(v),edges,first,stars)==(row['vertices'],row['edges'],
                     int(row['lowerFirst']),int(row['upperOrderedStars'])),t
        from fractions import Fraction
        from math import factorial
        y=max(Fraction(0),Fraction(first,S*S)-Fraction(stars,2*S**3))
        estimate=Fraction(10**15)/sum(y**j/factorial(j) for j in range(7))
        assert -(-estimate.numerator//estimate.denominator)==int(row['survivalUpper'])
        print('verified',t,'edges',edges,flush=True)


if __name__=='__main__':
    ap=ArgumentParser()
    ap.add_argument('table',type=Path)
    replay(json.loads(ap.parse_args().table.read_text()))

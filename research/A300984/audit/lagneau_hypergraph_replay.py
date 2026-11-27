"""Recompute all rounded two/three-large-prime Janson statistics independently."""
from argparse import ArgumentParser
from fractions import Fraction
from math import factorial,isqrt
from pathlib import Path
import json
import numpy as np
from lagneau_wide_replay import odd_prime_bits


def run(t):
    D,B,S=t['cap'],t['B'],t['precision']
    prime=odd_prime_bits(2*D)
    potential=np.arange(B+1+B%2,D//(B+1)+1,2,dtype=np.int64)
    vertices=potential[(prime(potential)!=0)&(prime(2*potential-1)==0)]
    del potential
    for row in t['rows']:
        a=row['small']
        v=vertices if not a else vertices[prime(2*a*vertices-1)==0]
        n=len(v)
        lower=S//v
        upper=(S+v-2)//(v-1)
        vs=np.zeros(n,dtype=np.int64)
        vsq=np.zeros(n,dtype=np.int64)
        ts=np.zeros(n,dtype=np.int64)
        cuts=[]
        for i,x in enumerate(v):
            stop=int(v.searchsorted(D//((B+1)*int(x)),side='right'))
            if stop<=i+1:break
            cuts.append(stop)
        offsets=np.cumsum([0]+[end-i-1 for i,end in enumerate(cuts)],dtype=np.int64)
        pairFlag=np.zeros(offsets[-1],dtype=np.uint8)
        pairSum=np.zeros(offsets[-1],dtype=np.int64)
        pairSq=np.zeros(offsets[-1],dtype=np.int64)

        def active(prefix,start,end):
            xs=v[start:end]
            keep=prime(2*prefix*xs-1)!=0
            if a:
                cut=int(xs.searchsorted(D//(prefix*a),side='right'))
                keep[:cut]|=prime(2*a*prefix*xs[:cut]-1)!=0
            return np.flatnonzero(keep)+start

        edgecount=edgefirst=0
        for i in range(int(v.searchsorted(isqrt(D),side='right'))):
            r=int(v[i])
            hit=active(r,i+1,int(v.searchsorted(D//r,side='right')))
            edgecount+=len(hit)
            edgefirst+=int(lower[i])*int(lower[hit].sum())
            h=upper[hit]
            vs[i]+=h.sum()
            vsq[i]+=(h*h).sum()
            vs[hit]+=upper[i]
            vsq[hit]+=upper[i]**2
            if i<len(cuts):
                short=hit[hit<cuts[i]]
                pairFlag[offsets[i]+short-i-1]=1
        ntri=tfirst=0
        for i,r0 in enumerate(v):
            r=int(r0)
            if r**3>=D:break
            for j in range(i+1,int(v.searchsorted(isqrt(D//r),side='right'))):
                rs=r*int(v[j])
                hit=active(rs,j+1,int(v.searchsorted(D//rs,side='right')))
                if not hit.size:continue
                ntri+=len(hit)
                tfirst+=int(lower[i])*int(lower[j])*int(lower[hit].sum())
                h=upper[hit]
                hs=h.sum()
                ts[i]+=upper[j]*hs
                ts[j]+=upper[i]*hs
                ts[hit]+=upper[i]*upper[j]
                ij=offsets[i]+j-i-1
                ik=offsets[i]+hit-i-1
                jk=offsets[j]+hit-j-1
                pairSum[ij]+=hs
                pairSq[ij]+=(h*h).sum()
                pairSum[ik]+=upper[j]
                pairSq[ik]+=upper[j]**2
                pairSum[jk]+=upper[i]
                pairSq[jk]+=upper[i]**2
        vstar=sum(int(w)*((int(g)*S+int(tr))**2-S*S*int(sq))
                  for w,g,tr,sq in zip(upper,vs,ts,vsq))
        pstar=0
        for i,end in enumerate(cuts):
            for k in np.flatnonzero(pairSum[offsets[i]:offsets[i+1]]):
                key=offsets[i]+k
                z=int(pairSum[key])
                term=2*int(pairFlag[key])*S*z+z*z-int(pairSq[key])
                pstar+=int(upper[i])*int(upper[i+1+k])*term
        assert (n,edgecount,ntri,edgefirst,tfirst,vstar,pstar)==(
            row['vertices'],row['edges'],row['triples'],int(row['lowerEdgeFirst']),
            int(row['lowerTripleFirst']),int(row['upperVertexStars']),int(row['upperPairStars'])),a
        mu=Fraction(edgefirst,S*S)+Fraction(tfirst,S**3)
        delta=Fraction(vstar,S**5)+Fraction(pstar,S**4)
        x=max(Fraction(),mu-delta/2)
        estimate=Fraction(10**15)/sum(x**j/factorial(j) for j in range(7))
        assert -(-estimate.numerator//estimate.denominator)==int(row['survivalUpper'])
        print('verified',a,'edges',edgecount,'triples',ntri,flush=True)


if __name__=='__main__':
    ap=ArgumentParser()
    ap.add_argument('table',type=Path)
    run(json.loads(ap.parse_args().table.read_text()))

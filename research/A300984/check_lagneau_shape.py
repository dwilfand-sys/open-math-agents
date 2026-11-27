"""Verify A300984 directly from its two divisor sums and characterize the observed support."""
from argparse import ArgumentParser
from math import isqrt


def terms(limit):
    squarefree=bytearray([1])*(limit+1)
    squarefree[0]=0
    for root in range(2,isqrt(limit)+1):
        step=root*root
        squarefree[step::step]=bytes(limit//step)
    total=[0]*(limit+1)
    sf=[0]*(limit+1)
    for d in range(1,limit+1):
        for n in range(d,limit+1,d):
            total[n]+=d
        if squarefree[d]:
            for n in range(d,limit+1,d):
                sf[n]+=d
    bound=max(total)
    sq=bytearray([1])*(bound+1)
    sq[0]=0
    for d in range(2,isqrt(bound)+1):
        sq[d*d::d*d]=bytes(bound//(d*d))
    return [(n,sf[n],total[n]-sf[n]) for n in range(1,limit+1)
            if sq[sf[n]] and sq[total[n]-sf[n]]]


def prime_factors(n):
    factors={}
    p=2
    while p*p<=n:
        while n%p==0:
            factors[p]=factors.get(p,0)+1
            n//=p
        p+=1 if p==2 else 2
    if n>1:
        factors[n]=1
    return factors


if __name__=='__main__':
    parser=ArgumentParser()
    parser.add_argument('limit',type=int,default=300000,nargs='?')
    result=terms(parser.parse_args().limit)
    for n,s,t in result:
        factors=prime_factors(n)
        assert factors.pop(2,0)>=2 and len(factors)==1
        p,j=next(iter(factors.items()))
        assert p%12==1 and j>=2 and s==3*(1+p)
    print(f'{len(result)} terms; first 15:', [n for n,_,_ in result[:15]])

"""Count the distinct primes in A300984 at powers of ten using its proved prime shape."""
from argparse import ArgumentParser
from functools import cache
from math import isqrt
from sympy import divisors, factorint, isprime, primerange


@cache
def is_squarefree(n):
    return n > 0 and all(e == 1 for e in factorint(n).values())


def is_a082539(p):
    return not any(d < p+1 and isprime(d-1) for d in divisors(p+1))


def smallest_term(p, bound):
    s=3*(p+1)
    if not is_squarefree(s):
        return None
    best=bound+1
    pj=p*p
    psum=1+p+pj
    while 4*pj < best:
        n=4*pj
        two_sigma=7
        while n < best:
            if is_squarefree(two_sigma*psum-s):
                best=n
                break
            two_sigma=2*two_sigma+1
            n*=2
        pj*=p
        psum+=pj
    return best if best <= bound else None


def records(max_power):
    bound=10**max_power
    seen=[]
    for p in primerange(13,isqrt(bound//4)+1):
        if p%12!=1: continue
        first=smallest_term(p,bound)
        if first is not None:
            seen.append((p,first,is_a082539(p)))
    return seen


if __name__=='__main__':
    parser=ArgumentParser()
    parser.add_argument('power',type=int,default=10,nargs='?')
    args=parser.parse_args()
    rows=records(args.power)
    for m in range(7,args.power+1):
        subset=[r for r in rows if r[1]<=10**m]
        good=sum(r[2] for r in subset)
        print(m,len(subset),good, f'{good/len(subset):.4%}', flush=True)
        if m==7:
            print('excluded at 10^7:',[p for p,_,g in subset if not g])

"""Verify a sampled A300984 certificate without the software used to factor it."""

from argparse import ArgumentParser
from functools import lru_cache
from gzip import open as gzip_open
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path
from random import Random
import json


def mr64(n):
    if n<2:
        return False
    if n%2==0:
        return n==2
    d = n-1
    s = 0
    while d%2==0:
        d//=2
        s+=1
    # Sorenson and Webster, "Strong pseudoprimes to twelve prime bases",
    # Math. Comp. 86 (2017). Their proved threshold is greater than 2**64.
    bases = [2,3,5,7,11,13,17,19,23,29,31,37]
    for a in bases:
        if not a%n:
            continue
        y = pow(a,d,n)
        if y in (1,n-1):
            continue
        for _ in range(s-1):
            y = y*y%n
            if y == n-1:
                break
        else:
            return False
    return True


def binomial(t,a,num=1,den=2):
    # Exact tail numerator followed by an upward-rounded decimal display.
    complement=den-num
    term=total=complement**t
    for j in range(1,a+1):
        term=term*(t+1-j)*num//(j*complement)
        total+=term
    total_den=den**t
    scale=10**12
    upper=(total*scale+total_den-1)//total_den
    return f"{upper//scale}.{upper%scale:012d}"


def main():
    cmd=ArgumentParser()
    cmd.add_argument('file')
    a=cmd.parse_args()
    path=Path(a.file)
    if path.suffix=='.gz':
        with gzip_open(path, 'rt', encoding='utf8') as src:
            cap=json.load(src)
    else:
        cap=json.loads(path.read_text(encoding='utf8'))
    limit=10**cap['m']
    maxprime=isqrt(limit//4)
    tests=cap['primality_certificates']
    @lru_cache(None)
    def verified(q):
        if q<2**64:
            return mr64(q)
        if str(q) not in tests:
            return False
        factors,bs=tests[str(q)]
        if prod(factors)!=q-1 or not all(verified(f) for f in set(factors)):
            return False
        for r in set(factors):
            a=bs[str(r)]
            if pow(a,q-1,q)!=1 or gcd(pow(a,(q-1)//r,q)-1,q)!=1:
                return False
        return True
    small_squares = [r*r for r in range(5,1001) if verified(r)]
    upper = lower = all_primitive = 0
    samples = cap['sample']
    assert len(samples)==cap['sample_size']
    rng=Random(cap['seed'])
    for p,factors,pr in samples:
        while True:
            drawn=12*rng.randint(1,(maxprime-1)//12)+1
            if drawn==p:
                break
            if mr64(drawn) and not any(((drawn+1)//2)%s==0 for s in small_squares):
                # A skipped prime must fail the squarefree eligibility test.
                from sympy import factorint
                skipped=factorint((drawn+1)//2)
                assert any(e>=2 and ((drawn+1)//2)%(r*r)==0 for r,e in skipped.items())
        assert p<=maxprime and p%12==1 and mr64(p)
        assert prod(factors)==(p+1)//2 and len(factors)==len(set(factors))
        assert all(mr64(r) for r in factors)
        has_obstruction=False
        for size in range(1,len(factors)):
            for subset in combinations(factors,size):
                if mr64(2*prod(subset)-1):
                    has_obstruction=True
        assert pr == (not has_obstruction)
        if pr:
            all_primitive+=1
            # Any representation must have j>=2 and i>=2. A verified square
            # divisor at *every* admissible exponent pair excludes p.
            possible=False
            power=p*p
            ps=1+p+power
            while 4*power <= limit:
                z,twos=4*power,7
                while z<=limit:
                    v=twos*ps-3*(p+1)
                    if not any(v%s==0 for s in small_squares):
                        possible=True
                        break
                    twos, z=2*twos+1,2*z
                if possible: break
                power*=p
                ps+=power
            upper+=possible
        elif str(p) in cap['witnesses']:
            n,v,fs=cap['witnesses'][str(p)]
            a,rem=divmod(n,p*p)
            assert rem==0 and a>=4 and not a&(a-1) and n<=limit
            assert v==(2*a-1)*(p*p+p+1)-3*(p+1)
            assert prod(fs)==v and len(fs)==len(set(fs))
            assert all(verified(f) for f in fs)
            lower+=1
    print('m',cap['m'],'sample',len(samples),'eligible primitive',all_primitive,
          'represented primitive upper',upper,'represented nonprimitive lower',lower)
    # In a simple random sample, under a population majority, for *true*
    # counts U>=A and L<=B the one-sided sign-test p-value can only get
    # smaller when U drops or L increases; report its conservative bound.
    print('sample ratio upper',upper/(upper+lower),'one-sided sign-test p upper',
          binomial(upper+lower,upper))
    print('one-sided p upper against population share >=49%',
          binomial(upper+lower,upper,49,100))


if __name__=='__main__':
    main()

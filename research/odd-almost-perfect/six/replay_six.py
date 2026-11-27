"""Verify an odd almost-perfect certificate using exact fractions and independent prime bounds."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import isqrt, prod
from pathlib import Path
import gzip
import sys
from typing import NamedTuple

ROOT=Path(__file__).parent
TWO=Fraction(2)
SMALL_LIMIT=200_000
small_divisors=[x for x in range(3,isqrt(SMALL_LIMIT)+1,2)
                if all(x%d for d in range(3,isqrt(x)+1,2))]

class Bounds(NamedTuple):
    first:int
    last:int|None
    exponent:int
    cap:int|None

@lru_cache(maxsize=12000)
def allowed_small_prime(x):
    return x>=3 and x%2==1 and all(x==d or x%d for d in small_divisors if d*d<=x)

@lru_cache(maxsize=100000)
def next_lower(x):
    x=max(3,x|1)
    while x<=SMALL_LIMIT and not allowed_small_prime(x):
        x+=2
    return x

@lru_cache(maxsize=100000)
def next_upper(x):
    x-=1-x%2
    while 3<=x<=SMALL_LIMIT and not allowed_small_prime(x):
        x-=2
    return x

def order(rows):
    answer=[]
    for i,(lo,hi,e,f) in enumerate(rows):
        lo=next_lower(max(lo,answer[-1].first+2) if i else lo)
        if hi is not None and hi<lo or f is not None and f<e:
            return None
        answer.append(Bounds(lo,hi,e,f))
    for i in reversed(range(len(answer))):
        lo,hi,e,f=answer[i]
        if i+1<len(answer) and answer[i+1].last is not None:
            cap=answer[i+1].last-2
            hi=min(hi,cap) if hi is not None else cap
        if hi is not None:
            hi=next_upper(hi)
            if hi<lo: return None
        answer[i]=Bounds(lo,hi,e,f)
    return tuple(answer)

@lru_cache(maxsize=64)
def character_works(p8,e8):
    geometric=sum(pow(p8,j,8) for j in range(e8+1))%8
    supplement=1 if geometric in (1,7) else -1
    reciprocity=-1 if p8%4==3 and geometric%4==3 else 1
    return supplement*reciprocity==1

def enforce_character(rows):
    result=[]
    for lo,hi,e,cap in rows:
        if cap==e:
            while not character_works(lo%8,e%8):
                lo=next_lower(lo+2)
            while hi is not None and hi>=lo and not character_works(hi%8,e%8):
                hi=next_upper(hi-2)
            if hi is not None and hi<lo: return None
        if hi==lo:
            while not character_works(lo%8,e%8): e+=2
            if cap is not None and cap<e: return None
        result.append(Bounds(lo,hi,e,cap))
    return order(result)

@lru_cache(maxsize=120000)
def value(p,e):
    # Sum of reciprocal powers, directly over a common denominator.
    numerator=sum(pow(p,j) for j in range(e+1))
    return Fraction(numerator,pow(p,e))

def ends(c):
    lo=Fraction(1) if c.last is None else value(c.last,c.exponent)
    hi=Fraction(c.first,c.first-1) if c.cap is None else value(c.first,c.cap)
    return lo,hi

def core_bounds(rows):
    for _ in range(3):
        lower,upper=zip(*(ends(c) for c in rows))
        total_l,total_u=prod(lower),prod(upper)
        result=[]
        for j,c in enumerate(rows):
            low=total_l/lower[j]
            high=total_u/upper[j]
            if low>=TWO: return None
            left=TWO/(TWO-low)
            lo=max(c.first,left.numerator//left.denominator)
            hi=c.last
            if high<TWO:
                right=TWO/(TWO-high)
                cap=(right.numerator-1)//right.denominator
                hi=cap if hi is None else min(cap,hi)
            result.append(Bounds(lo,hi,c.exponent,c.cap))
        result=order(result)
        if result is None or result==rows: return result
        rows=result
    return rows

@lru_cache(maxsize=12000)
def geometric_values(m,p,e,cap):
    x=pow(p,e,m)
    s=sum(pow(p,j,m) for j in range(e+1))%m
    values=set();seen=set()
    while (x,s) not in seen and (cap is None or e<=cap):
        seen.add((x,s));values.add(s)
        s=(s+x*p*(p+1))%m
        x=x*p*p%m
        e+=2
    return values

def mod_failure(rows):
    fixed=[c.first for c in rows if c.first==c.last]
    for c in rows:
        if c.first==c.last and c.exponent==c.cap:
            s=sum(pow(c.first,j) for j in range(c.exponent+1))
            if any(s%p==0 for p in fixed): return True
    moduli=[m for m in (3,5,7,11,13) if m in fixed]+[16]
    for mod in moduli:
        vals={1}
        for c in rows:
            if c.first==c.last: rs={c.first%mod}
            elif c.last is not None and c.last-c.first<mod:
                rs={x%mod for x in range(c.first,c.last+1,2)}
            else:
                rs=range(mod) if mod%2 else range(1,mod,2)
            local=set().union(*(geometric_values(mod,r,c.exponent,c.cap) for r in rs))
            vals={x*y%mod for x in vals for y in local}
        if ((1 if mod==16 else -1)%mod) not in vals: return True
    return False

def verify(k):
    blob=gzip.decompress((ROOT/f"odd_{k}_certificate.gz").read_bytes())
    assert blob[:5]==b"APB1"+bytes([k])
    stream=iter(blob[5:])
    stack=[[Bounds(3,None,2,None)]*k]
    counts=Counter()
    for tag in stream:
        rows=stack.pop()
        counts[tag]+=1
        if rows is not None:
            rows=order(rows)
        if rows is not None:
            rows=enforce_character(rows)
        if rows is not None:
            rows=core_bounds(rows)
        if tag in range(6):
            if rows is None: continue
            if tag<3: raise ValueError(("unverified empty region",tag,rows))
            if tag==3: assert prod(ends(c)[0] for c in rows)>=2
            elif tag==4:
                nmin=prod(c.first**c.exponent for c in rows)
                assert prod(ends(c)[1] for c in rows)+Fraction(1,nmin)<2
            else: assert mod_failure(rows)
            continue
        cut=0;shift=0
        while True:
            x=next(stream)
            cut|=(x&127)<<shift
            if x<128: break
            shift+=7
            assert shift<256
        is_prime=16<=tag<16+k
        assert is_prime or 32<=tag<32+k
        if rows is None:
            stack.extend([None,None]);continue
        i=tag-(16 if is_prime else 32)
        c=rows[i]
        if is_prime:
            l=Bounds(c.first,min(cut,c.last) if c.last is not None else cut,c.exponent,c.cap)
            r=Bounds(max(c.first,cut+1),c.last,c.exponent,c.cap)
        else:
            assert cut>=0 and cut%2==0
            l=Bounds(c.first,c.last,c.exponent,min(cut,c.cap) if c.cap is not None else cut)
            r=Bounds(c.first,c.last,max(c.exponent,cut+2),c.cap)
        stack.append(rows[:i]+(l,)+rows[i+1:])
        stack.append(rows[:i]+(r,)+rows[i+1:])
    assert not stack
    print(f"Verified all {sum(counts.values())} nodes for {k} prime factors",flush=True)

if __name__=="__main__":
    for item in sys.argv[1:]: verify(int(item))

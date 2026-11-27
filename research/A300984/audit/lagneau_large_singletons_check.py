"""Independently count the large singleton pairs using ordinary odd Eratosthenes."""
from argparse import ArgumentParser
from math import isqrt


def sieve_primes(limit):
    flags = bytearray([1])*(limit+1)
    flags[:2] = b'\0\0'
    for i in range(2,isqrt(limit)+1):
        if flags[i]:
            flags[i*i::i] = bytes((limit-i*i)//i+1)
    return [i for i in range(3,limit+1,2) if flags[i]]


def odd_segment(first,length,primes):
    last = first+2*(length-1)
    flags = bytearray([1])*length
    for q in primes:
        if q*q>last:
            break
        start = max(q*q, (first+q-1)//q*q)
        if start % 2 == 0:
            start += q
        pos = (start-first)//2
        if pos<length:
            flags[pos::q] = bytes((length-1-pos)//q+1)
    return flags


def run(lower,upper):
    from operator import and_
    base = sieve_primes(isqrt(2*upper))
    scale = 10**15
    factor = scale
    first, stop = (lower-1)//6+1, (upper-1)//6+1
    total = 0
    for k in range(first,stop,65536):
        size = min(stop-k,65536)
        lo = 6*k+1
        hi = lo + 6*(size-1)
        flags = odd_segment(lo,3*size-2,base)[::3]
        shifted = odd_segment(2*lo-1,6*size-5,base)[::6]
        assert len(flags)==len(shifted)==size
        count = sum(map(and_,flags,shifted))
        total += count
        factor = (factor*hi+hi+count-1)//(hi+count)
    return total,factor


if __name__=='__main__':
    ap = ArgumentParser()
    ap.add_argument('lower',nargs='?',type=int,default=20_000_000)
    ap.add_argument('upper',nargs='?',type=int,default=1_000_000_000)
    a = ap.parse_args()
    assert 5<=a.lower<a.upper
    print('prime pairs and multiplier in units of 10^-15:',run(a.lower,a.upper))

"""Recompute the A085267 finite and middle-range certificates using integers."""

import re
from bisect import bisect_right
from fractions import Fraction as Q
from math import isqrt, prod
from pathlib import Path


EXCEPTIONS = (1, 2, 3, 4, 5, 8, 9, 13, 25, 29, 61)
MASK = 2305843009784128319


def finite():
    limit = 365000
    sf = bytearray([1]) * (limit + 1)
    sf[0] = 0
    for d in range(2, isqrt(limit) + 1):
        q = d*d
        sf[q::q] = bytes(limit // q)
    exceptions = []
    largest_second_root = 0
    for n in range(1, limit+1):
        found = 0
        for k in range(1, min(17, isqrt(n-1))+1):
            found += sf[n-k*k]
            if found == 2:
                largest_second_root = max(largest_second_root, k)
                break
        else:
            assert sum(sf[n-k*k] for k in range(1, isqrt(n-1)+1)) <= 1, n
            exceptions.append(n)
    assert tuple(exceptions) == EXCEPTIONS
    assert largest_second_root == 17
    assert 1 + sum(1 << n for n in exceptions) == MASK
    # Independent bit-parallel simulation of the recurrence in the Lean candidate.
    flags = int.from_bytes(bytes(sum(1 << i for i in range(8) if j+i <= limit and sf[j+i])
                                 for j in range(0, limit+1, 8)), byteorder='little')
    whole = (1 << (limit+1))-1
    none = at_most_one = whole
    for k in range(1, 18):
        failed = whole & ~(flags << (k*k))
        at_most_one, none = none | (at_most_one & failed), none & failed
    assert at_most_one == MASK
    print("Two independent first-17-root checks reproduced the 11 exact "
          "exceptions through 365,000 and the Lean bit mask.")


def primes_to(limit):
    flags = bytearray([1]) * (limit+1)
    flags[:2] = bytes(2)
    for d in range(2, isqrt(limit)+1):
        if flags[d]:
            flags[d*d::d] = bytes((limit-d*d)//d+1)
    return [p for p in range(2, limit+1) if flags[p]]


def moderate(leanfile):
    source = leanfile.read_text(encoding='utf-8').split('def rows :', 1)[1].split(']', 1)[0]
    rows = [tuple(map(int, row)) for row in re.findall(r'\((\d+), (\d+), (\d+)\)', source)]
    assert len(rows) == 80
    limit = 2_000_001
    primes = primes_to(limit)
    # Count positive integers prime to the wheel by ordinary sieving.
    rough = bytearray([1]) * (limit+1)
    rough[0] = 0
    for p in primes[:bisect_right(primes, 101)]:
        rough[p::p] = bytes(limit//p)
    rough_positive = [n for n in range(1, limit+1) if rough[n]]
    first = [3, 5, 7, 11, 13, 17]
    profiles = [[p for i,p in enumerate(first) if mask & (1<<i)] for mask in range(64)]
    next_lo = 300
    combinations = 0
    min_margin = None
    for lo,hi,cost in rows:
        assert lo == next_lo and hi>=lo
        next_lo = hi+1
        qcost = sum(2*hi//(p*p) for p in primes[1:bisect_right(primes, isqrt(2*hi))])
        assert cost == bisect_right(rough_positive, 2*hi+1)+24+qcost
        actual = bisect_right(primes, 2*hi+1)-1+qcost
        assert actual <= cost
        for small in profiles:
            numerator,denominator = prod(p-1 for p in small),prod(small)
            refund = sum(2*hi//(p*p)+1 for p in small)
            for t in range(5):
                if denominator > 2*hi+2:
                    break
                rank = len(small)+t
                error = 1<<(rank-1) if rank else 0
                margin = Q(lo*numerator,denominator)-cost+refund-error
                assert margin > 1, (lo,hi,small,t,margin)
                min_margin = margin if min_margin is None else min(min_margin,margin)
                combinations += 1
                numerator *= 18
                denominator *= 19
    assert next_lo == 1_000_001
    print(f"All 80 consecutive interval bounds and {combinations:,} admissible "
          f"prime profiles passed. Smallest proved count lower bound: {min_margin}.")


def large():
    groups = [
        (10**6, Q(36,125),Q(1,4),22000+Q(1,4),64),
        (2400000,Q(34,125),Q(1,4),22000+Q(1,4),128),
        (55*10**6,Q(1,4),Q(2,9),262145+Q(2,9),512),
    ]
    for j, coefficient, prime_slope, prime_intercept, max_pow in groups:
        slope = coefficient-prime_slope-Q(1,128)
        assert slope>0 and slope*j-prime_intercept-61*max_pow > 100
    assert Q(87,50)-Q(8,5)-Q(1,16)-Q(1,100) == Q(27,400)
    assert Q(27,400)*4*8**10 > 100
    assert len([i for i in range(1,62) if i not in EXCEPTIONS]) == 50
    print("The three large-range rational bounds, high-rank margin and "
          "one-based index shift of 11 were checked.")


if __name__=='__main__':
    import sys
    leanfile = Path(sys.argv[1]) if len(sys.argv)>1 else Path('proofs/oeis-a085267.lean')
    finite()
    moderate(leanfile)
    large()

"""Uniform samples of structurally eligible primes, with one-sided representation tests."""

import argparse
from math import prod
from random import Random
from sympy import factorint, isprime, primerange


SQUARES = [q*q for q in primerange(5, 1001)]


def primitive(k_factors):
    # For p+1=2k the smaller obstruction primes are exactly 2d-1 for proper d|k.
    factors = sorted(k_factors)
    k = prod(factors)
    divisors = [1]
    for f in factors:
        for d in divisors[:]:
            e = d*f
            if e < k and e % 3 == 1 and isprime(2*e - 1):
                return False
            divisors.append(e)
    return True


def unresolved_witness(p, limit):
    j, power, ps = 2, p*p, 1+p+p*p
    while 4*power <= limit:
        n, ts = 4*power, 7
        while n <= limit:
            v = ts*ps-3*(p+1)
            if all(v % qq for qq in SQUARES):
                return True
            ts, n = 2*ts+1, 2*n
        j, power = j+1, power*p
        ps += power
    return False


def run(m, size, seed):
    from math import isqrt
    rng = Random(seed)
    X = isqrt(10**m//4)
    n_eligible = n_prim = n_pos = n_p_pos = 0
    while n_eligible < size:
        p = 12*rng.randint(1, (X-1)//12)+1
        if not isprime(p):
            continue
        factors = factorint((p+1)//2)
        if any(e>1 for e in factors.values()):
            continue
        n_eligible += 1
        pr = primitive(factors)
        pos = unresolved_witness(p, 10**m)
        n_prim += pr
        n_pos += pos
        n_p_pos += pr and pos
    print(m, size, n_prim, n_pos, n_p_pos, 'ratios',
          n_prim/size, n_p_pos/n_pos, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('size', type=int)
    p.add_argument('m', type=int, nargs='+')
    p.add_argument('--seed', type=int, default=31415926)
    a = p.parse_args()
    for m in a.m:
        run(m, a.size, a.seed+m)

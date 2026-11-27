"""Enumerate recurrent-prime cores for Lagneau's two divisor-sum questions.

Stripping exponent-one prime factors multiplies both divisor sums by the
same product. Each remaining core is uniquely a²b³ with squarefree b.
"""
from argparse import ArgumentParser
from math import isqrt


def small_primes(n):
    table = bytearray(b'\x01') * (n + 1)
    table[:2] = b'\x00\x00'
    for p in range(2, isqrt(n)+1):
        if table[p]:
            table[p*p::p] = b'\x00' * ((n-p*p)//p+1)
    return [i for i in range(2,n+1) if table[i]]


def counterexamples(limit):
    primes = small_primes(isqrt(limit))
    visited = 0
    positive = []

    def visit(value, pos, total, sf):
        nonlocal visited
        visited += 1
        if total > sf and total % sf == 0:
            d = total // sf - 1
            root = isqrt(d)
            if root*root == d and (root == 1 or any(root % p == 0 for p in primes if p*p <= root)):
                positive.append((value, sf, root))
        for i in range(pos, len(primes)):
            p = primes[i]
            if value*p*p > limit:
                break
            power = p*p
            sigma = 1+p+power
            while value*power <= limit:
                visit(value*power, i+1, total*sigma, sf*(1+p))
                power *= p
                sigma += power

    visit(1, 0, 1, 1)
    return visited, sorted(positive)


if __name__ == '__main__':
    parser=ArgumentParser()
    parser.add_argument('limit',type=int)
    args=parser.parse_args()
    count, examples=counterexamples(args.limit)
    print(f'{count} cores through {args.limit}; {len(examples)} composite-or-unit square ratios')
    for record in examples:
        print(*record)

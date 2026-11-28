"""Certify the ten intermediate bands for 101 positive-square representations.

Codex for dwilfand-sys. This is the middle of the proof for OEIS A085264.
For J >= 1,000,000 the independent A085267 large-range proof supplies 101.
For n > 3,202^2 there are J >= 1,600 parity-compatible candidate roots.

For the current J, S contains the odd prime square factors of n and
A = S intersect {3,5,7,11,13,17}. Set t = |S\\A| and E(0)=0,
E(k)=2^(k-1) otherwise. The large-prime-set product bound implies
(prod A)*19^t <= 2*J+2 and t <= 4. If P(2J+1) <= alpha*J for the odd
prime counting function P, and active odd primes p^2 <= 2J have reciprocal
square sum <= R, removing A bounds the loss by
J*(alpha+2*(R-sum_{p in A} 1/p^2))-|A|.
Before subtracting those losses, the candidate count is at least
J*prod_{p in A}(1-1/p)*(18/19)^t-E.
Every checked strict surplus is after reserving 100, so integer counts are
at least 101. The eligible-profile slope is positive, hence its value at the
first admissible J bounds the whole interval.

The binomial interval estimate used in the seven dyadic bands is
P(x) <= P(m) + floor(x/e) for m <= x <= 2m and 2^e <= m+1.
This follows since every newly counted prime divides binom(x,m) <= 2^x.
When x=2J+1 and m=J+1, P(m)=P(2*floor(J/2)+1). The last fact excludes only
an even integer >2. Small reciprocal caps use ordinary exact summation.
The large cap sums primes through 128, then majorizes odd integers q>128
by 1/q^2 <= (1/(q-1)-1/(q+1))/2; the telescoping tail is <= 1/256.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt, prod


ROWS = [
    (1600, 2047, 2950, 199283), (2048, 4095, 2780, 200323),
    (4096, 8191, 2700, 205000), (8192, 16383, 2889, 205000),
    (16384, 32767, 2874, 205000), (32768, 65535, 2771, 205000),
    (65536, 131071, 2636, 205000), (131072, 262143, 2495, 205000),
    (262144, 524287, 2359, 205000), (524288, 1000000, 2233, 205000),
]
SMALL = (3, 5, 7, 11, 13, 17)
PRIMES = [n for n in range(3, 16384, 2)
          if all(n % d for d in range(3, isqrt(n) + 1, 2))]


def prime_seeds(lo, hi, alpha):
    """Cover J by exact monotone upper estimates, and return their witnesses."""
    start = lo
    rows = []
    while start <= hi:
        end = start
        while end <= hi and sum(p <= 2*end+1 for p in PRIMES) <= alpha*start:
            end += 1
        assert end > start
        upper = end - 1
        x = 2*upper+1
        cnt = sum(p <= x for p in PRIMES)
        assert cnt <= alpha*start
        rows.append((start, upper, x, cnt))
        start = end
    return rows


def audit():
    least = None
    seeds = []
    cases = 0
    for i, (lo, hi, a, r) in enumerate(ROWS):
        alpha, cap = Q(a, 10000), Q(r, 1000000)
        assert lo == (1600 if i == 0 else ROWS[i-1][1] + 1)
        if i < 3:
            seeds.extend(prime_seeds(lo, hi, alpha))
        else:
            old_l, old_h, old_a, _ = ROWS[i-1]
            assert old_l <= lo//2 and hi//2 <= old_h
            e = (lo+2).bit_length()-1
            assert 2**e <= lo+2 and Q(old_a,20000)+Q(2,e)+Q(1,e*lo) <= alpha
        if hi <= 4095:
            bound = sum((Q(1,p*p) for p in PRIMES if p*p<=2*hi), Q(0))
        else:
            bound = sum((Q(1,p*p) for p in PRIMES if p<=128), Q(1,256))
        assert bound <= cap
        for k in range(len(SMALL)+1):
            for A in combinations(SMALL,k):
                D, rho = prod(A), prod(Q(p-1,p) for p in A)
                refund = sum((Q(1,p*p) for p in A), Q(0))
                for t in range(5):
                    first = max(lo, (D*19**t-1)//2)
                    if first > hi:
                        continue
                    slope = rho*Q(18,19)**t-alpha-2*(cap-refund)
                    error = 2**(k+t-1) if k+t else 0
                    surplus = first*slope-(100+error-k)
                    assert slope > 0 and surplus > 0
                    record = (surplus,first,A,t)
                    if least is None or record < least:
                        least = record
                    cases += 1
    assert ROWS[-1][1] == 1000000
    assert len(seeds) == 27 and cases == 1457
    assert least == (Q(23899061,3705625),1600,(5,7,11),0)
    return seeds, cases, least


if __name__ == '__main__':
    seeds, cases, least = audit()
    print('27 prime-count anchors (start, end, integer endpoint, odd-prime count):')
    print(seeds)
    print(f'{len(ROWS)} bands, {cases} admissible profiles, least strict surplus {least}.')

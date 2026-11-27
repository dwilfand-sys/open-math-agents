"""Check the rational sieve and all odd squares up to 10**10 independently."""
from fractions import Fraction
from math import isqrt, prod
from itertools import combinations, product
from hashlib import sha256
from pathlib import Path

bounds = [
    (3, Fraction(13, 9), Fraction(13, 9)),
    (3, Fraction(121, 81), Fraction(3, 2)),
    (5, Fraction(31, 25), Fraction(5, 4)),
    (7, Fraction(57, 49), Fraction(7, 6)),
    (11, Fraction(133, 121), Fraction(11, 10)),
    (13, Fraction(183, 169), Fraction(13, 12)),
    (17, Fraction(1), Fraction(17, 16)),
]
cutoff = Fraction(255, 128)

for k in range(1, 4):
    count = 0
    for bands in product(bounds, repeat=k):
        if not all(a[0] != b[0] or a[0] == 17 for a, b in combinations(bands, 2)):
            continue
        count += 1
        assert prod(b[2] for b in bands) <= cutoff or 2 <= prod(b[1] for b in bands)
    print(k, "prime bands:", count, "compatible lists checked")

def factors(n):
    fac = []
    p = 3
    while p*p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            fac.append((p, e))
        p += 2
    if n > 1:
        fac.append((n, 1))
    return fac

all_cases = 0
three_cases = 0
for root in range(1, 100_001, 2):
    fac = factors(root)
    n = root * root
    sigma = prod((p**(2*e+1)-1)//(p-1) for p,e in fac)
    assert sigma % 2 == 1
    all_cases += 1
    if len(fac) <= 3:
        assert sigma * 128 <= 255*n or 2*n <= sigma
        three_cases += 1
    assert root == 1 or sigma + 1 != 2*n
print("Odd squares checked:", all_cases, "with at most three prime factors:", three_cases)
print("Largest odd square checked:", 99_999**2)

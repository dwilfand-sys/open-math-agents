"""Certify finite representation counts and intermediate sieve margins for A085264.

Run with Python 3.10 or newer. Only the standard library is required.
"""

from bisect import bisect_right
from fractions import Fraction
from math import isqrt, prod


MAX_LEVEL = 100
FIRST_J = 1600
LAST_J = 1_000_000
FINITE_LIMIT = (2 * FIRST_J + 2) ** 2
EXACT_PREFIX = 200_000


def primes_to(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def squarefree_mask(limit):
    flags = bytearray(b'\x01') * (limit + 1)
    flags[0] = 0
    for p in primes_to(isqrt(limit)):
        square = p * p
        flags[square::square] = bytes(limit // square)
    packed = bytearray((limit + 8) // 8)
    for i, value in enumerate(flags):
        if value:
            packed[i // 8] |= 1 << (i % 8)
    return int.from_bytes(packed, 'little')


def at_most(planes, level, mask):
    equal, below = mask, 0
    for bit in reversed(range(max(len(planes), level.bit_length()))):
        digits = planes[bit] if bit < len(planes) else 0
        if level & (1 << bit):
            below |= equal & ~digits
            equal &= digits
        else:
            equal &= ~digits
    return below | equal


def finite_counts():
    source = squarefree_mask(FINITE_LIMIT)
    whole = (1 << (FINITE_LIMIT + 1)) - 1
    prefix = (1 << (EXACT_PREFIX + 1)) - 2  # n=1,...,EXACT_PREFIX
    exterior = whole & ~(prefix | 1)
    planes = []
    for k in range(1, isqrt(FINITE_LIMIT) + 1):
        carry = (source << (k * k)) & whole
        bit = 0
        while carry and bit < len(planes):
            carry, planes[bit] = carry & planes[bit], carry ^ planes[bit]
            bit += 1
        if carry:
            planes.append(carry)
        if k * k >= EXACT_PREFIX and (k % 64 == 0 or k == isqrt(FINITE_LIMIT)):
            if not at_most(planes, MAX_LEVEL, exterior):
                break
    else:
        raise AssertionError('Exterior needs explicit low-level classification')
    levels = []
    for level in range(MAX_LEVEL + 1):
        hits = prefix
        for bit, digits in enumerate(planes):
            hits &= digits if level & (1 << bit) else ~digits
        levels.append((hits.bit_count(), hits.bit_length() - 1))
    print('finite limit', FINITE_LIMIT, 'all exterior counts certified by roots through', k, flush=True)
    print('counts', [v[0] for v in levels], flush=True)
    print('last', [v[1] for v in levels], flush=True)


def large_margins():
    # Pi_odd(128)=30 and these three cardinality cases use a cutoff of 128.
    for lower_j, coefficient, prime_slope, prime_constant, max_power in [
            (1_000_000, Fraction(36, 125), Fraction(1, 4), Fraction(88_001, 4), 64),
            (2_400_000, Fraction(34, 125), Fraction(1, 4), Fraction(88_001, 4), 128),
            (55_000_000, Fraction(1, 4), Fraction(2, 9), Fraction(2, 9) + 262_145, 512)]:
        slope = coefficient - prime_slope - Fraction(1, 128)
        margin = slope * lower_j - prime_constant - 61 * max_power
        assert slope > 0 and margin > MAX_LEVEL
        print('large bound', lower_j, 'minimum margin', margin, flush=True)
    # For r>=10, J/r >= 4*8^r and the sieve leaves at least (27/400)*J/r.
    assert Fraction(27, 400) * 4 * 8**10 > MAX_LEVEL


def moderate_intervals():
    primes = primes_to(2 * LAST_J + 1)[1:]
    small = primes[:6]
    profiles = []
    for mask in range(1 << len(small)):
        factors = tuple(p for j, p in enumerate(small) if mask & (1 << j))
        for t in range(5):
            denom = prod(factors) * 19**t
            numer = prod(p - 1 for p in factors) * 18**t
            rank = len(factors) + t
            profiles.append((factors, denom, numer, 2**(rank-1) if rank else 0))

    def min_slack(lo, hi):
        end = bisect_right(primes, isqrt(2 * hi))
        cost = bisect_right(primes, 2 * hi + 1) + sum((2 * hi) // (p*p) for p in primes[:end])
        return min(Fraction(lo * numer, denom) - cost + sum(1 + (2*hi) // (p*p) for p in factors) - error
                   for factors, denom, numer, error in profiles if denom <= 2 * hi + 2)

    lo = FIRST_J
    total = 0
    minimum = None
    while lo <= LAST_J:
        hi = min(LAST_J, lo + lo // 24)
        slack = min_slack(lo, hi)
        while slack <= MAX_LEVEL and hi > lo:
            hi = (lo + hi) // 2
            slack = min_slack(lo, hi)
        assert slack > MAX_LEVEL, (lo, hi, slack)
        minimum = min(minimum, slack) if minimum is not None else slack
        total += 1
        lo = hi + 1
    print('intermediate certificate', total, 'intervals; minimum margin', minimum, flush=True)


if __name__ == '__main__':
    large_margins()
    moderate_intervals()
    finite_counts()

"""Check a squarefree-sieve bound for all square divisors B up to a given size.

This is an independent integer-arithmetic certificate for the moderate range,
separate from the Lean proof for squarefree inputs. It bounds the lower count
of roots coprime to B and counts opposite pairs for primes not dividing B.
"""

from bisect import bisect_right
from fractions import Fraction
from math import isqrt, prod


def prime_table(limit):
    table = bytearray([1]) * (limit + 1)
    table[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if table[p]:
            table[p * p :: p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(3, limit + 1) if table[p]]


def cost(j, primes):
    return bisect_right(primes, 2 * j + 1) + sum(
        2 * j // (p * p) for p in primes[: bisect_right(primes, isqrt(2 * j))]
    )


def certificate(start_j=300, end_j=1_000_000):
    primes = prime_table(2 * end_j + 1)
    small = [3, 5, 7, 11, 13, 17]
    tail = [p for p in primes if p > small[-1]]
    if any(x <= 0 for x in (start_j, end_j)) or end_j < start_j:
        raise ValueError("nonempty positive range required")
    blocks = tests = 0
    lo = start_j
    while lo <= end_j:
        hi = min(end_j, lo + lo // 60)
        upper_weight = cost(hi, primes)
        for mask in range(1 << len(small)):
            es = [p for i, p in enumerate(small) if (mask >> i) & 1]
            numerator = prod(p - 1 for p in es)
            denominator = prod(es)
            refund = sum(2 * hi // (p * p) + 1 for p in es)
            tail_size = 0
            while denominator <= 2 * hi + 2:
                r = len(es) + tail_size
                error = (1 << (r - 1)) if r else 0
                assert lo * numerator > (upper_weight - refund + error) * denominator, (
                    lo, hi, es, tail_size
                )
                tests += 1
                q = tail[tail_size]
                numerator *= q - 1
                denominator *= q
                tail_size += 1
        blocks += 1
        lo = hi + 1
    return blocks, tests


def finite_witnesses(limit):
    squarefree = bytearray([1]) * (limit + 1)
    squarefree[0] = 0
    for d in range(2, isqrt(limit) + 1):
        square = d * d
        squarefree[square::square] = bytes(limit // square)
    failures = []
    max_root = 0
    for n in range(1, limit + 1):
        for k in range(1, isqrt(n - 1) + 1):
            if squarefree[n - k * k]:
                max_root = max(k, max_root)
                break
        else:
            failures.append(n)
    assert failures == [1, 13]
    return max_root


def large_range_constants():
    odd = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    assert sum(Fraction(1, p * p) for p in odd) + Fraction(1, 76) < Fraction(21, 100)
    scale = Fraction(29, 50)
    for r in range(10):
        if r <= 6:
            expected = Fraction(36, 125)
        elif r == 7:
            expected = Fraction(34, 125)
        else:
            expected = Fraction(1, 4)
        density_with_three = prod(Fraction(p - 1, p) for p in odd[:r])
        density_without_three = prod(Fraction(p - 1, p) for p in odd[1:1 + r])
        assert expected <= scale * density_without_three
        assert expected <= (scale + Fraction(2, 9)) * density_with_three
    assert prod(odd[:7]) >= 2 * 2_400_000 + 2
    assert prod(odd[:8]) >= 2 * 55_000_000 + 2
    rows = [(6, 1_000_000, Fraction(36, 125), 16, 22_000),
            (7, 2_400_000, Fraction(34, 125), 16, 22_000),
            (9, 55_000_000, Fraction(1, 4), 18, 262_144)]
    for r, j, coefficient, power, base in rows:
        assert coefficient - Fraction(4, power) - Fraction(1, 128) > 0
        loss = base + Fraction(4*j+4, power) + Fraction(j, 128) + 63*2**r
        assert coefficient*j > loss
    assert len(prime_table(128)) == 30
    assert prod(odd[:10]) >= 8 * 10 * 8**10 + 2
    assert prod(Fraction(p - 1, p) for p in odd[:10]) > Fraction(3, 10)
    assert Fraction(87, 50) > Fraction(8, 5) + Fraction(1, 16) + Fraction(1, 100)
    assert 100*(16*10+1) <= 4*4**10


if __name__ == "__main__":
    print("Finite exceptions [1, 13]; largest first root", finite_witnesses(365_000))
    print("Blocks and exact profile inequalities", *certificate())
    large_range_constants()
    print("Infinite-range base estimates and exact rational margins passed")

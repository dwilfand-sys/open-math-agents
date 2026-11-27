"""Independent checks of the lower bound and prime-by-prime attaining pairs."""

import argparse
import math
import random


def primes_to(m):
    return [p for p in range(2, m + 1)
            if all(p % d for d in range(2, math.isqrt(p) + 1))]


def vfact(x, p):
    result = 0
    while x:
        x //= p
        result += x
    return result


def order(x, p):
    assert x > 0
    count = 0
    while x % p == 0:
        x //= p
        count += 1
    return count


def ratio_val(m, n, s, p):
    return (vfact(m * n, p) + vfact(m * s, p) - vfact(n, p) - vfact(s, p)
            - (m - 1) * vfact(n + s, p))


def normalization(m):
    return m * math.factorial(m) // math.lcm(*range(1, m + 1))


def attaining_pair(m, p):
    t_power = 1
    while t_power * p <= m:
        t_power *= p
    t = t_power - 1
    big_power = 1
    while big_power <= m * (p + 1):
        big_power *= p
    first = t * big_power // m + 1
    n = first + (1 - first) % p
    s = big_power - n
    assert 0 < n < big_power and m * n // big_power == t and m * n % big_power
    return n, s


def exact_grid(limit, side):
    factorial = [math.factorial(x) for x in range(limit * side + 1)]
    count = 0
    attained = []
    for m in range(1, limit + 1):
        scale = normalization(m)
        gcd = 0
        for n in range(side + 1):
            for s in range(n, side + 1):
                if n + s == 0:
                    continue
                numerator = factorial[m * n] * factorial[m * s]
                denominator = factorial[n] * factorial[s] * factorial[n + s] ** (m - 1)
                ratio, remainder = divmod(numerator, denominator)
                assert remainder == 0 and ratio % scale == 0, (m, n, s)
                gcd = math.gcd(gcd, ratio)
                count += 1
        if gcd == scale:
            attained.append(m)
    print(f"Lower bound: {count} nonzero-sum pairs by exact factorial arithmetic.")
    print(f"The finite grid already attained the gcd for {len(attained)}/{limit} arities.")


def large_valuations(limit, samples):
    rng = random.Random(20261127)
    count = 0
    witnesses = 0
    for m in range(1, limit + 1):
        scale = normalization(m)
        # Include two primes beyond the possible support of m! as a boundary check.
        primes = primes_to(m + 25)
        prime_set = [p for p in primes if p <= m] + [p for p in primes if p > m][:2]
        for p in prime_set:
            expected = order(scale, p)
            for _ in range(samples):
                n, s = rng.randrange(10**9), rng.randrange(10**9)
                assert ratio_val(m, n, s, p) >= expected
                assert ratio_val(m, p * n, p * s, p) == ratio_val(m, n, s, p)
                count += 1
            n, s = attaining_pair(m, p)
            assert ratio_val(m, n, s, p) == expected, (m, p, n, s)
            witnesses += 1
    print(f"Lower bound: {count} large prime-valuation checks, including scaling invariance.")
    print(f"Upper bound: {witnesses} independently evaluated constructive witnesses.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--grid-arity", type=int, default=40)
    parser.add_argument("--grid-side", type=int, default=24)
    parser.add_argument("--valuation-arity", type=int, default=200)
    parser.add_argument("--samples", type=int, default=16)
    args = parser.parse_args()
    if args.grid_arity < 2 or args.grid_side < 1 or args.valuation_arity < 1:
        parser.error("positive ranges and grid arity at least two are required")
    exact_grid(args.grid_arity, args.grid_side)
    large_valuations(args.valuation_arity, args.samples)

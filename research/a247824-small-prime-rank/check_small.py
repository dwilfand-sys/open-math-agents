"""Two independent calculations of the first numerical child of upstream PR #9315."""
from functools import cache
from math import isqrt
import sys

sys.setrecursionlimit(20_000)
limit = 20_868_472
cut = 4_568


def trial_prime(t):
    return t >= 2 and all(t % d != 0 for d in range(2, isqrt(t) + 1))


ps = [p for p in range(cut + 1) if trial_prime(p)]


@cache
def legendre(i, x):
    if not i:
        return x, 1
    p = ps[i - 1]
    if x < p:
        return int(x > 0), 1
    a, na = legendre(i - 1, x)
    b, nb = legendre(i - 1, x // p)
    return a - b, na + nb + 1


def sieve_prime_count(x):
    sieve = bytearray([1]) * (x + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(x) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytes((x - p * p) // p + 1)
    return sum(sieve)


if __name__ == "__main__":
    phi, calls = legendre(len(ps), limit)
    independent = sieve_prime_count(limit)
    assert len(ps) == sieve_prime_count(cut)
    assert phi + len(ps) == independent + 1 == 1_322_164
    print(f"pi({limit}) = {independent:,}, pi({cut}) = {len(ps)},"
          f" rough phi = {phi:,}")
    print(f"Function evaluations before memoization {calls:,},"
          f" distinct subproblems {legendre.cache_info().currsize:,}.")

"""Certify a prime r < q², r = 2 mod 3, q | r+2 for each prime q in [lo, hi].

SymPy proposes witnesses. An independent segmented sieve verifies each proposal.
"""

import argparse
import bisect
import math

from sympy import isprime


def primes_through(bound):
    sieve = bytearray([1]) * (bound + 1)
    sieve[:2] = bytes(2)
    for q in range(2, math.isqrt(bound) + 1):
        if sieve[q]:
            sieve[q * q :: q] = bytes(len(sieve[q * q :: q]))
    return [q for q in range(2, bound + 1) if sieve[q]]


def certify(values):
    values = sorted(set(values))
    trial = primes_through(math.isqrt(values[-1]))
    size = 1 << 20
    next_index = 0
    while next_index < len(values):
        lo = (values[next_index] // size) * size
        hi = min(lo + size, values[-1] + 1)
        sieve = bytearray([1]) * (hi - lo)
        for d in trial:
            if d * d >= hi:
                break
            start = max(d * d, (lo + d - 1) // d * d) - lo
            if start < len(sieve):
                sieve[start::d] = bytes(len(sieve[start::d]))
        stop = bisect.bisect_left(values, hi, next_index)
        for r in values[next_index:stop]:
            if r < 2 or not sieve[r - lo]:
                raise ValueError(f"Witness {r} failed direct sieve")
        next_index = stop


def check(lo, hi):
    primes = [q for q in primes_through(hi) if q >= lo]
    values = []
    worst_k = (0, 0)
    largest = (0, 0)
    for q in primes:
        k = 1 if q % 3 == 1 else 5
        while not isprime(k * q - 2) or k * q - 2 <= 5:
            k += 6
        r = k * q - 2
        assert 5 < r < q * q and r % 3 == 2 and (r + 2) % q == 0
        values.append(r)
        worst_k = max(worst_k, (k, q))
        largest = max(largest, (r, q))
    print(len(primes), "moduli; largest (k,q)", worst_k,
          "largest (r,q)", largest, flush=True)
    certify(values)
    print(f"Direct sieves verified all primes q in [{lo},{hi}] and their witnesses.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lo", type=int)
    parser.add_argument("hi", type=int)
    args = parser.parse_args()
    if not 5 <= args.lo <= args.hi:
        parser.error("require 5 <= lo <= hi")
    check(args.lo, args.hi)

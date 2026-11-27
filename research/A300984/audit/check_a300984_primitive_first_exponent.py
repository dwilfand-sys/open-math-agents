"""Exact bounds for squarefreeness of F_2 among eligible primitive primes."""

from fractions import Fraction
from math import isqrt


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def first_exponent_bounds(cutoff=10_000):
    assert cutoff >= 8 and cutoff % 2 == 0
    # A primitive p>13 has v_7(p+1)=0, since 13+1=14.
    local_product = Fraction(1)
    upper = Fraction(1)
    split_primes = 0
    for r in range(5, cutoff, 2):
        if r == 7 or not is_prime(r):
            continue
        if pow(-96, (r - 1) // 2, r) == 1:
            split_primes += 1
            local_product *= 1 - Fraction(2, r * (r - 2))
            denominator = r * (r - 2) if is_prime(2 * r - 1) else r * (r - 1) - 1
            upper *= 1 - Fraction(2, denominator)
    # Sum of 2/[n(n-2)] over odd n > cutoff is 1/(cutoff-1).
    return local_product * (1 - Fraction(1, cutoff - 1)), upper, split_primes


if __name__ == "__main__":
    lower, upper, count = first_exponent_bounds()
    assert count == 610 and lower > Fraction(8412, 10_000)
    assert upper < Fraction(8703, 10_000)
    print(f"{count} split primes. Outward-rounded interval: "
          f"[{int(10**9 * lower)}/10^9, {int(10**9 * upper) + 1}/10^9].")

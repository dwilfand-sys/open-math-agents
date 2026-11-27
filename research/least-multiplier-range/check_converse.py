"""Exact arithmetic checks of the rough-abundancy construction for the OEIS converse."""
from fractions import Fraction
from math import isqrt


def primes_below(limit):
    prime = bytearray([1]) * limit
    prime[:2] = bytes(2)
    for p in range(2, isqrt(limit - 1) + 1):
        if prime[p]:
            count = (limit - 1 - p * p) // p + 1
            prime[p * p::p] = bytes(count)
    return [p for p in range(limit) if prime[p]]


def check(k, primes, sigma):
    x = k - 1
    a = Fraction(2 * k, 2 * k - 1)
    b = Fraction(2 * x, 2 * x - 1)
    min_prime = max(k, a // (b - a)) + 1
    sigma_n = n = 1
    for p in primes:
        if p < min_prime:
            continue
        assert a * (1 + Fraction(1, p)) < b
        sigma_n *= p + 1
        n *= p
        if sigma_n * a.denominator >= n * a.numerator:
            break
    assert a <= Fraction(sigma_n, n) < b
    assert (2 * k - 1) * sigma_n >= 2 * k * n
    for m in range(1, k):
        if sigma[m] < 2 * m:
            assert sigma[m] * sigma_n < 2 * m * n
    if sigma[k] + 1 == 2 * k:
        assert sigma[k] * sigma_n >= 2 * k * n


def divisor_sigma_table(limit):
    sigma = [0] * (limit + 1)
    for divisor in range(1, limit + 1):
        for n in range(divisor, limit + 1, divisor):
            sigma[n] += divisor
    return sigma


def check_prime_arguments(primes, sigma, bound):
    almost = [k for k in range(1, bound + 1) if sigma[k] + 1 == 2 * k]
    checked = 0
    for p in primes:
        if p <= 2:
            continue
        if p > bound:
            break
        # All k tested satisfy k < p. Multiplication of sigma is exact for these coprime factors.
        actual = next(k for k in range(1, p)
                      if sigma[k] < 2 * k and sigma[k] * (p + 1) >= 2 * k * p)
        formula = next(k for k in almost if p + 1 <= 2 * k)
        assert actual == formula
        checked += 1
    return checked


if __name__ == "__main__":
    bound = 500
    primes = primes_below(600_000)
    sigma = divisor_sigma_table(bound * bound)
    for k in range(2, bound + 1):
        check(k, primes, sigma)
    image = set()
    for n in range(2, bound + 1):
        value = next(m for m in range(1, bound + 1)
                     if sigma[m] < 2 * m and sigma[m * n] >= 2 * m * n)
        assert value == 3 or sigma[value] + 1 == 2 * value
        image.add(value)
    print(f"Confirmed all {bound - 1} construction intervals and all smaller deficient"
          f" multipliers, including every known almost-perfect input up to {bound}.")
    print(f"By direct exhaustive enumeration, the distinct values a(2), ..., a({bound})"
          f" are {sorted(image)}.")
    count = check_prime_arguments(primes, sigma, 10_000)
    print(f"The exact prime-argument formula matched all {count} odd primes through 10,000.")

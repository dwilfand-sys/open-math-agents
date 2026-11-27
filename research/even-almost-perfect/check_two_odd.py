"""Independent checks for TwoOddPowers.lean. Run with Python 3 and SymPy."""
from hashlib import sha256
from itertools import product
from pathlib import Path

import sympy as sp


def check_polynomials():
    p, r, q, P, R, X, Y = sp.symbols("p r q P R X Y")
    z = (p - 1) * (r - 1)
    w = p + r - 1
    C = (q + 1) * w - p * r
    A = C * (q + 2) + 3 * q

    base = (1 + q * X * Y - (q + 1) * P * R) * z
    powers = q * (X * (p - 1) * Y * (r - 1) - (p * P - 1) * (r * R - 1))
    cleared = C * P * R + q + z - q * (p * P + r * R)
    assert sp.expand(base - powers - cleared) == 0

    square = q * (p**2 + p + 1) * (r**2 + r + 1) + 1 - (q + 1) * p**2 * r**2
    assert sp.expand(square - (w * (A - w) - (C**2 - 3 * q - 1))) == 0


def check_geometric_sums():
    count = 0
    for level in range(4, 101, 4):
        for p in range(level + 1, level + 17):
            for r in range(p + 1, level + 32):
                for a, b in product((2, 4, 6, 8, 10), repeat=2):
                    xp = (p ** (a + 1) - 1) // (p - 1)
                    xr = (r ** (b + 1) - 1) // (r - 1)
                    assert 1 + (level - 1) * xp * xr != level * p**a * r**b
                    count += 1
    return count


def check_even_numbers(limit):
    sigma = [0] * (limit + 1)
    odd_prime_count = bytearray(limit + 1)
    for divisor in range(1, limit + 1):
        for n in range(divisor, limit + 1, divisor):
            sigma[n] += divisor
        if divisor > 2 and sigma[divisor] == divisor + 1:
            for n in range(divisor, limit + 1, divisor):
                odd_prime_count[n] += 1

    one_prime = two_primes = powers_of_two = 0
    for n in range(2, limit + 1, 2):
        if n & (n - 1) == 0:
            assert sigma[n] + 1 == 2 * n
            powers_of_two += 1
        elif odd_prime_count[n] <= 2:
            assert sigma[n] + 1 != 2 * n
            one_prime += odd_prime_count[n] == 1
            two_primes += odd_prime_count[n] == 2
    return powers_of_two, one_prime, two_primes


if __name__ == "__main__":
    check_polynomials()
    print("Confirmed both symbolic identities.")
    print(f"Confirmed {check_geometric_sums():,} geometric-sum inequalities.")
    power, one, two = check_even_numbers(500_000)
    print(f"Through 500,000: {power:,} powers of two, {one:,} with one odd prime,"
          f" and {two:,} with two odd primes.")
    print("Lean SHA256", sha256(Path(__file__).with_name("TwoOddPowers.lean").read_bytes()).hexdigest())

"""Exact certificate for the A279821 prime-cube witness; Python standard library."""

from math import comb, isqrt


def central_mod(power, prime, modulus):
    """Use term ratios in the exact multinomial expansion. All divisors are units."""
    assert 0 <= power < 2 * prime
    term = total = 1
    for j in range(1, power // 2 + 1):
        numerator = (power - 2*j + 2) * (power - 2*j + 1)
        term = term * numerator * pow(j*j, -1, modulus) % modulus
        total = (total + term) % modulus
    return total


def central_at_prime_by_recurrence(p):
    """Second calculation via n*T_n=(2n-1)*T_(n-1)+3(n-1)*T_(n-2)."""
    modulus = p**5
    t0 = t1 = 1
    for n in range(2, p):
        numerator = (2*n-1)*t1 + 3*(n-1)*t0
        t0, t1 = t1, numerator * pow(n, -1, modulus) % modulus
    numerator = ((2*p-1)*t1 + 3*(p-1)*t0) % modulus
    assert numerator % p == 0
    return numerator // p


def main():
    p = 205129
    assert all(p % j for j in range(2, isqrt(p) + 1))
    for k in range(25):
        exact = sum(comb(k, 2*j) * comb(2*j, j) for j in range(k//2 + 1))
        assert central_mod(k, p, p**4) == exact % p**4
    residue = central_mod(p, p, p**4)
    assert residue == central_at_prime_by_recurrence(p)
    assert residue == 1 + 79027 * p**3
    print(f"p = {p}, p^3 = {p**3}")
    print(f"T(p) mod p^4 = {residue}")
    print(f"(T(p) - 1)/p^3 mod p = {(residue-1)//(p**3)}")


if __name__ == "__main__":
    main()

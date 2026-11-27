"""Exact local certificates for two A279821 witnesses. Python standard library."""

from functools import cache
from math import comb, isqrt, prod


@cache
def coefficient(power, degree=0):
    """Coefficient of x^degree in (x^-1+1+x)^power."""
    degree = abs(degree)
    return sum(comb(power, j + degree) * comb(power-j-degree, j)
               for j in range((power-degree)//2+1))


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def modulo_prime_square(n, p):
    """CT recurrence from expanding f^p=f(x^p)+pG, for small p."""
    modulus = p*p

    @cache
    def rec(t):
        if t < p:
            return coefficient(t) % modulus
        m, d = divmod(t, p)
        center = (coefficient(p+d) - coefficient(d)) // p
        side = (coefficient(p+d, p) - coefficient(d)) // p
        # Only degrees 0 and ±p of G*f^d can interact with f(x^p)^(m-1).
        # Symmetry and CT(f^m)=CT(f^(m-1))+2[x]f^(m-1) give the formula.
        return ((coefficient(d) + p*m*side)*rec(m) +
                p*m*(center-side)*rec(m-1)) % modulus

    return rec(n)


def chinese(congruences):
    modulus = prod(m for _, m in congruences)
    return sum(a*(modulus//m)*pow(modulus//m, -1, m)
               for a, m in congruences) % modulus


def verify(n, small, q):
    factors = small + [q]
    assert len(set(factors)) == len(factors) and all(map(prime, factors))
    assert prod(factors) == n and n > 6_000_000
    # For q>3 Sun proved T(q)=1 mod q². The same expansion at d=0
    # gives T(qm)=T(m) mod q², since the endpoint terms of G vanish.
    residues = [(modulo_prime_square(n, p), p*p) for p in small]
    residues.append((coefficient(n//q) % (q*q), q*q))
    assert all(a % p == 1 for (a, _), p in zip(residues, factors))
    full = chinese(residues)
    assert full % n == 1 and full != 1
    print(n, residues, full, 'mod', n*n)


if __name__ == '__main__':
    for p in (2, 3, 5, 7, 11):
        for t in range(121):
            assert modulo_prime_square(t, p) == coefficient(t) % (p*p)
    verify(1_316_632_279, [31], 42_472_009)
    verify(1_793_930_422, [2, 37], 24_242_303)

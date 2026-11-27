"""Finite audit of the gcd exclusions and the two-large-prime switching identity."""

from math import gcd, isqrt


def prime_factor_sieve(limit):
    factor = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if factor[p] == p:
            for n in range(p * p, limit + 1, p):
                if factor[n] == n:
                    factor[n] = p
    return factor


def factors(n, sieve):
    while n != 1:
        p = sieve[n]
        yield p
        n //= p


def check(cap=150_000, rough=19):
    # p in (cap/2,cap], giving n=2p-1 and 4p+1 <= 4cap+1.
    sieve = prime_factor_sieve(4 * cap + 1)
    limit = 2 * cap - 1
    min_gcd = [limit + 1] * (limit + 1)
    for a in range(2, isqrt(2 * limit) + 1):
        for b in range(a, 2 * limit // (a + 1) + 1):
            g = gcd(a, b)
            n = (a*b + a + b - g) // 2
            if n <= limit and min_gcd[n] > g:
                min_gcd[n] = g

    # Use an actual integer cutoff with z^4 > 4cap+1, allowing repeated q=r.
    z = 37
    assert z**4 > 4*cap+1 and rough < z
    survived = split = strong = double = equal = blocked_rough = 0
    for p in range(cap // 2 + 1, cap + 1):
        if p % 3 != 1 or sieve[p] != p:
            continue
        n = 2*p - 1
        if min(factors(n, sieve)) <= rough:
            continue
        inert = [s for s in factors(4*p+1, sieve) if s % 4 == 3]
        if any(s < z for s in inert):
            continue
        survived += 1
        if not inert:
            split += 1
            assert min_gcd[n] > rough
            if min_gcd[n] == limit+1:
                strong += 1
            else:
                blocked_rough += 1
        else:
            assert len(inert) == 2
            q, r = inert
            k = (4*p+1)//(q*r)
            assert all(s % 4 == 1 for s in factors(k, sieve))
            assert q >= z and r >= q and k*z*z <= 4*cap+1
            double += 1
            if q == r:
                equal += 1
    assert survived == split + double
    print(f"{survived} small-sifted primes in ({cap//2}, {cap}], "
          f"{split} fully split values and {double} with a pair of inert factors "
          f"({equal} repeated).")
    print(f"Among the split examples, {strong} actual strong exceptions, "
          f"{blocked_rough} have minimum representing gcd greater than {rough}.")


if __name__ == "__main__":
    check()

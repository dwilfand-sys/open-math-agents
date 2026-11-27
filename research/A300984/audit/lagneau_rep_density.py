"""Bound the limiting fraction of eligible primes missed by three A300984 witnesses.

Run with Python 3.10 or later. Only the standard library is required.
For a prime p = 1 mod 12 with 3(p+1) squarefree, use n = 2**i * p**2
with i = 2, 3, 4. Its nonsquarefree-divisor sum is
F_i(p) = A*p**2 + (A-3)*(p+1), where A = 2**(i+1)-1.

The finite local densities follow from the prime number theorem in fixed
arithmetic progressions and the Chinese remainder theorem. Passing from a
finite square-divisor sieve to its limiting density also uses the quadratic
squarefree tail argument. This script certifies the numerical comparison.
"""

from fractions import Fraction
from math import isqrt


CUTOFF = 20_000
SCALE = 10**12
COEFFICIENTS = (7, 15, 31)


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p) // p + 1)
    return [p for p in range(5, limit + 1) if sieve[p]]


def square_divisor_roots(q, a):
    """Number of admissible unit residues mod q² satisfying F_i(p) = 0."""
    b = a - 3
    if b % q == 0:
        # F_i is a nonzero multiple of p² mod q, with no unit root.
        return 0
    if a % q == 0:
        # One simple root mod q. Its lift is the excluded -1 iff q² divides A.
        return int(a % (q*q) != 0)
    discriminant = -3 * b * (a + 1)
    assert discriminant % q != 0  # a+1 is a power of two.
    return 2 if pow(discriminant % q, (q-1)//2, q) == 1 else 0


def verify_local_counts(q, counts):
    """Directly check the formulas and disjointness for small moduli."""
    modulus = q*q
    roots = [set() for _ in COEFFICIENTS]
    for r in range(modulus):
        if r % q == 0 or r + 1 == modulus:
            continue
        for j, a in enumerate(COEFFICIENTS):
            if (a*r*r + (a-3)*(r+1)) % modulus == 0:
                roots[j].add(r)
    assert [len(part) for part in roots] == counts
    assert len(set.union(*roots)) == sum(counts)


def finite_failure_bounds():
    # For each subset of the three witnesses, maintain scaled outward bounds
    # on the Euler product for the event that all witnesses in it survive.
    subsets = range(1 << len(COEFFICIENTS))
    lower = [SCALE for _ in subsets]
    upper = lower.copy()
    for q in primes_through(CUTOFF):
        counts = [square_divisor_roots(q, a) for a in COEFFICIENTS]
        if q <= 97:
            verify_local_counts(q, counts)
        # Condition on p and p+1 being admissible. Remove the nonunits and
        # the single class -1 from all q² residue classes.
        denominator = q*q - q - 1
        for subset in subsets:
            # F_(i+t) - 2**t F_i = (2**t-1)(p+2)². A common root
            # mod q² would force q|p+2, impossible since F_i(-2)=3(A+1).
            excluded = sum(c for j, c in enumerate(counts) if subset & (1 << j))
            numerator = denominator - excluded
            lower[subset] = lower[subset] * numerator // denominator
            upper[subset] = (upper[subset] * numerator + denominator - 1) // denominator

    # Inclusion-exclusion now gives the probability that each of the first
    # k witnesses has at least one forbidden square divisor q², with q≤CUTOFF.
    bounds = []
    for k in range(1, len(COEFFICIENTS) + 1):
        failure_low = failure_high = 0
        for subset in range(1 << k):
            if subset.bit_count() % 2:
                failure_low -= upper[subset]
                failure_high -= lower[subset]
            else:
                failure_low += lower[subset]
                failure_high += upper[subset]
        bounds.append((failure_low, failure_high))
    return bounds


def main():
    bounds = finite_failure_bounds()
    for k, (lower, upper) in enumerate(bounds, start=1):
        print(f"First {k} witnesses all fail the finite sieve: [{lower}, {upper}] / {SCALE}")

    # Let X = sqrt(bound)/2. The available numbers of witnesses are 1, 2, 3
    # on the successive shells (X/√2,X], (X/2,X/√2], (0,X/2].
    assert 2 * 707**2 < 1000**2 < 2 * 708**2
    weight_upper = (Fraction(293, 1000), Fraction(208, 1000), Fraction(1, 2))
    small_prime_loss = sum(w * Fraction(hi, SCALE) for w, (_, hi) in zip(weight_upper, bounds))

    # The limiting contribution for each polynomial beyond the cutoff is
    # ≤ sum_{q odd > CUTOFF} 2/[q(q-2)] = 1/(CUTOFF-1), by telescoping.
    # Taking all three tails even in shells where fewer are available is safe.
    assert CUTOFF % 2 == 0
    total_loss = small_prime_loss + Fraction(len(COEFFICIENTS), CUTOFF - 1)
    assert total_loss < Fraction(46, 1000)
    print(f"Upper bound on limiting missed fraction: {total_loss} < 46/1000")
    print(f"Lower bound on limiting represented fraction: {1-total_loss} > 954/1000")


if __name__ == "__main__":
    main()

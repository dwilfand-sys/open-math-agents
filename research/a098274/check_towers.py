"""Exact finite tests of the positive-binomial proof for both A098274 towers.

Run with Python 3.8 or newer. Integers are exact throughout. The program
checks the stated implications separately and reports the bounds it tested.
"""

from collections import Counter
from math import comb


def valuation(a, p):
    """p-adic valuation of a nonzero (possibly negative) integer."""
    assert a
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def binomial_row(n):
    row = [1]
    for j in range(n):
        row.append(row[-1] * (n - j) // (j + 1))
    return row


def rising_row(n, last):
    values = [1]
    for j in range(last):
        values.append(values[-1] * (n + j + 1) // (j + 1))
    return values


def rows(n):
    """Yield ordinary / shifted terms and their independently constructed weights."""
    ordinary = binomial_row(n)
    shifted = binomial_row(n - 1) + [0]
    rise = rising_row(n, 2 * n)
    prev = rising_row(n - 1, 2 * n)
    for minus, choose, top in ((False, ordinary, rise), (True, shifted, prev)):
        terms = [choose[j] ** 2 * top[j] * top[2*j] for j in range(n+1)]
        # Index zero of the weight is not used.
        if minus:
            weights = [0] + [shifted[j] ** 2 * rise[j-1] * rise[2*j-1]
                             for j in range(1, n+1)]
        else:
            weights = [0] + [shifted[j-1] ** 2 * rise[j] * rise[2*j]
                             for j in range(1, n+1)]
        signed_row = (-1) ** (n - minus) * sum(
            (-1) ** j * choose[j] * top[j] ** 3 for j in range(n+1))
        assert sum(terms) == signed_row
        if n <= 120:
            actual = n - minus
            assert terms == [comb(actual, j) ** 2 * comb(actual+j, actual)
                             * comb(actual+2*j, actual) for j in range(n+1)]
        assert terms[0] == 1
        if minus:
            assert terms[n] == weights[n] == 0
        else:
            assert terms[n] == weights[n] == comb(2*n, n) * comb(3*n, n)
        yield minus, terms, weights


def check_adjacent(n, j, minus, w, wnext):
    """Independent division-free consecutive-binomial weight formulas."""
    if minus:
        denom = (j+1)**2 * j * (2*j) * (2*j+1)
        numer = (n-j-1)**2 * (n+j) * (n+2*j) * (n+2*j+1)
    else:
        denom = j*j * (j+1) * (2*j+1) * (2*j+2)
        numer = (n-j)**2 * (n+j+1) * (n+2*j+1) * (n+2*j+2)
    assert denom * wnext == numer * w


def check_aligned_ratios(p, r, m, i, count):
    """Test the three individual unit ratios and their predecessor identities."""
    v = r-1
    t = min(v, valuation(i, p)) if i else v
    exponent = 3+v+2*t
    for a, k in ((m, i), (m+i, i), (m+2*i, 2*i)):
        lower = comb(a, k)
        upper = comb(p*a, p*k)
        # Express v_p(upper/lower - 1) >= exponent over the integers.
        assert (upper-lower) % (p**(exponent+valuation(lower, p))) == 0
        assert comb(p*a-1, p*k)*lower == comb(a-1, k)*upper
        count["individual aligned ratio and predecessor identity"] += 1


def check_level(p, r, m, count, sharp):
    q = p**r
    modulus = q**3
    n = m*q
    low = n//p
    for i in range(low+1):
        check_aligned_ratios(p, r, low, i, count)
    for high_row, lower_row in zip(rows(n), rows(low)):
        minus, terms, weights = high_row
        _, lower, _ = lower_row
        name = "shifted" if minus else "ordinary"
        count["row comparisons"] += 1
        diff_row = sum(terms) - sum(lower)
        assert diff_row % modulus == 0
        if diff_row % (p*modulus) and name not in sharp:
            sharp[name] = (p, r, m, diff_row % (p*modulus))

        prefix = weighted = abel = 0
        off_sum = sum(t for j, t in enumerate(terms) if j % p)
        assert off_sum % modulus == 0
        for i in range(low+1):
            assert (terms[p*i] - lower[i]) % modulus == 0
            count["aligned " + name] += 1
            if i == 0 or i == low:
                count["aligned endpoint"] += 1
        for j in range(1, n+1):
            w = weights[j]
            u = pow(j, -2, q) if j % p else 0
            prefix = (prefix + u) % q
            weighted = (weighted + w*u) % q
            assert (1+minus)*j*j*terms[j] == n*n*w
            count["term clearing"] += 1
            if j == n:
                assert prefix == 0
                assert (weighted - (w * prefix - abel)) % q == 0
                break

            vals = [min(r, valuation(t, p)) for t in (j, j+1, 2*j+1)]
            for v, kind in zip(vals, ("j", "j+1", "2j+1")):
                assert prefix % (p**v) == 0
                if v:
                    count["positive jump " + kind] += 1
            # p >= 5 keeps these three kinds of jumps mutually exclusive.
            assert sum(bool(v) for v in vals) <= 1
            s = max(vals)
            dw = weights[j+1] - w
            check_adjacent(n, j, minus, w, weights[j+1])
            assert dw % (p**(r-s)) == 0
            assert dw * prefix % q == 0
            abel = (abel + dw * prefix) % q
            count["adjacent " + name] += 1
        assert weighted == 0
        assert ((1+minus)*off_sum - n*n*weighted) % modulus == 0


def main():
    count = Counter()
    sharp = {}
    # Keep r as specified even when p|m to test this separate quantifier.
    cases = {(p, r, m) for p in (5, 7, 11, 13, 17, 19, 23, 29, 31)
             for r in range(1, 5) for m in (1, 2, 3, 4, 5, 6, 7, p, 2*p)
             if m*p**r <= 750}
    for p, r, m in sorted(cases):
        check_level(p, r, m, count, sharp)
    print(f"{len(cases)} (p,r,m) triples, maximum n={max(m*p**r for p,r,m in cases)}.")
    for key in sorted(count):
        print(f"  {key}: {count[key]}")
    for name, (p, r, m, residue) in sharp.items():
        print(f"  Exact valuation {3*r} for {name}, p={p}, r={r}, m={m}, "
              f"row difference = {residue} modulo {p**(3*r+1)}.")


if __name__ == "__main__":
    main()

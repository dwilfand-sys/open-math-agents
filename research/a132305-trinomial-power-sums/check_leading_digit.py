"""Test a proposed p-adic leading digit for powers of trinomial coefficients.

The left side is computed from exact row coefficients, then reduced modulo
p^(2r + v_p(h) + 1) before dividing. The independent right side only uses
the base row at m and the mod-3 character. Python 3.8+.
"""

from collections import Counter
from functools import lru_cache


def chi(n):
    return (0, 1, -1)[n % 3]


@lru_cache(maxsize=12)
def half_row(n):
    """Coefficients through the middle of (1+x+x²)^n by differentiation."""
    entries = [1]
    last, current = 0, 1
    for k in range(1, n + 1):
        num = (n-k+1)*current + (2*n-k+2)*last
        new, rem = divmod(num, k)
        assert rem == 0
        entries.append(new)
        last, current = current, new
    return entries


@lru_cache(maxsize=None)
def elementary_row(n):
    """Separate Pascal construction for the right side and for controls."""
    row = [1]
    for _ in range(n):
        old = [0, 0] + row + [0, 0]
        row = [old[i] + old[i+1] + old[i+2] for i in range(len(old)-2)]
    return row


def analytic_side(p, m, h, r):
    row = elementary_row(m)
    inner = [sum(chi(d)*row[k-d] for d in range(1, k+1)) for k in range(2*m+1)]
    assert inner == [0] + elementary_row(m-1) + [0]
    b = sum(pow(t, h-1, p)*u for t, u in zip(row, inner)) % p
    harmonic = sum(pow(i, -2, p) for i in range(1, p//3+1)) % p
    return pow(chi(p), r-1, p) * harmonic * b * pow(3, -1, p) % p


def h_parts(p, h):
    order, unit = 0, h
    while unit % p == 0:
        unit //= p
        order += 1
    return order, unit


def row_residues(n, modulus):
    half = half_row(n)
    if n <= 70:
        assert half == elementary_row(n)[:n+1]
    return [t % modulus for t in half]


def moment(half, h, modulus):
    return (2 * sum(pow(t, h, modulus) for t in half[:-1])
            + pow(half[-1], h, modulus)) % modulus


def check(p, m, r, powers, count):
    n = m*p**r
    precision = p**(2*r + max(h_parts(p, h)[0] for h in powers) + 1)
    high = row_residues(n, precision)
    low = row_residues(n//p, precision)
    check_coefficients(p, m, r, high, low, count)
    for h in powers:
        order, unit = h_parts(p, h)
        denom_p = p**(2*r+order)
        modulus = p*denom_p
        difference = (moment(high, h, modulus) - moment(low, h, modulus)) % modulus
        got, rem = divmod(difference, denom_p)
        assert rem == 0, ("divisibility", p, m, r, h, rem)
        got = got * pow(m*m*unit, -1, p) % p
        expected = analytic_side(p, m, h, r)
        if h == 2:
            # The central specialization for A_2(N)=t(2N,2N) doubles the digit.
            expected = 2*expected % p
        assert got == expected, ("leading digit", p, m, r, h, got, expected)
        if h == 2:
            count["separate quadratic exception"] += 1
            continue
        count["digits"] += 1
        count["sharp" if got else "vanishing"] += 1
        if order:
            count["p divides h"] += 1
        if order >= 2:
            count["p squared divides h"] += 1
        if m > p:
            count["m > p"] += 1
        if m == 1:
            count["m = 1"] += 1
        if r >= 3:
            count["r >= 3"] += 1
        if p == 5:
            count["p = 5"] += 1
    count["tower levels"] += 1


def check_coefficients(p, m, r, high, low, count):
    # Endpoints j=0 and 2*n0 have zero continuation to the row n0-1.
    n0 = m*p**(r-1)
    denom_p = p**(2*r)
    harmonic = sum(pow(k, -2, p) for k in range(1, p//3+1)) % p
    previous = row_residues(n0-1, p)
    unit = pow(m*m, -1, p)
    for j in range(2*n0+1):
        k = min(j, 2*n0-j)
        diff = (high[p*k] - low[k]) % (p*denom_p)
        a, rem = divmod(diff, denom_p)
        assert rem == 0, ("coefficient divisibility", p, m, r, j, rem)
        got = a*unit % p
        rhs = 0 if k == 0 else harmonic*previous[k-1]*pow(3, -1, p) % p
        assert got == rhs, ("coefficient leading digit", p, m, r, j, got, rhs)
        count["coefficient digits"] += 1
        if got:
            count["nonzero coefficient digits"] += 1


def main():
    count = Counter()
    primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
    for p in primes:
        powers = sorted(set(range(2, 14)) | {p, p+1, 2*p, 3*p, p*p, 2*p*p, p**3})
        for m in sorted(set(range(1, 10)) | {p-1, p+1, p+2, 2*p-1, 2*p+1}):
            if m % p == 0:
                continue
            for r in range(1, 7):
                n = m * p**r
                # Longer towers at m=1, more coprime base indices elsewhere.
                cap = 17500 if m == 1 and p <= 13 else 2100
                if n > cap:
                    break
                check(p, m, r, powers, count)
    print(f"Primes {primes}")
    for name in sorted(count):
        print(f"{name}: {count[name]}")


if __name__ == "__main__":
    main()

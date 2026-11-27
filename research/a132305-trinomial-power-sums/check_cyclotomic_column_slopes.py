"""Test the polynomial column classification against exact, truncated integer powers."""

from fractions import Fraction


def multiply(a, b, cap):
    out = [0] * min(cap + 1, len(a) + len(b) - 1)
    for j, lhs in enumerate(a):
        for k in range(min(len(b), len(out) - j)):
            out[j+k] += lhs * b[k]
    return out


def power_column(f, exponent, j):
    res = [1]
    base = list(f)
    while exponent:
        if exponent % 2:
            res = multiply(res, base, j)
        exponent //= 2
        if exponent:
            base = multiply(base, base, j)
    return res[j] if j < len(res) else 0


def sums(f, cutoff):
    # Coefficients of -xF'(x)/F(x) are the power sums of the reciprocal roots.
    out = [0]
    for n in range(1, cutoff + 1):
        out.append(-(n * f[n] if n < len(f) else 0)
                   - sum(f[k] * out[n-k] for k in range(1, min(n+1, len(f)))))
    return out


def valuation(x, p):
    def at(n):
        assert n
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        return a
    return at(x.numerator) - at(x.denominator)


def check():
    # Third entry is the lcm of reciprocal-root orders if all are prime to p.
    examples = [(5, [1, 1], 2), (5, [1, 1, 1], 3), (7, [1, 1, 1], 3),
                (5, [1, -2, 1], 1), (7, [1, 0, 1], 4), (5, [1, -1, 1], 6),
                (5, [1, 2], None), (5, [1, 0, 1, 1], None),
                (5, [1, 0, 0, 0, 0, 1], None), (7, [1, 2, 3, -1], None)]
    checks = 0
    for p, f, period in examples:
        degree = len(f) - 1
        s = sums(f, p * max(degree, period or 1))
        if period is not None:
            j = period
            assert all(s[p*i] == s[i] for i in range(1, degree+1))
            slope = 2
            c = Fraction(p*p, 2) * sum(Fraction(s[i]**2, i*(p*j-i))
                                           for i in range(1, p*j) if i % p)
            assert c > 0
        else:
            j = next(k for k in range(1, degree+1) if s[p*k] != s[k])
            slope = 1
            c = Fraction(s[j] - s[p*j], j)
        for r in range(6, 12):
            lhs = power_column(f, p**(r+1), p*j) - power_column(f, p**r, j)
            assert valuation(lhs, p) == r*slope + valuation(c, p), (p, f, j, r)
            checks += 1
    print(f'{checks} exact large-level column valuations across {len(examples)} examples')


if __name__ == '__main__':
    check()

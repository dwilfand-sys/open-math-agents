"""Independently check the normalized first p-adic digit of trinomial moments."""

from collections import Counter


def half_row(n):
    # (1+x+x^2)f'(x) = n(1+2x)f(x). Reflection supplies indices past n.
    row = [1]
    for k in range(1, n + 1):
        left = row[k - 1] * (n - k + 1)
        right = row[k - 2] * (2 * n - k + 2) if k >= 2 else 0
        coefficient, remainder = divmod(left + right, k)
        assert remainder == 0
        row.append(coefficient)
    return row


def moment(row, h, modulus):
    return (2 * sum(pow(c % modulus, h, modulus) for c in row[:-1])
            + pow(row[-1] % modulus, h, modulus)) % modulus


def coefficient(row, j):
    n = len(row) - 1
    if j < 0 or j > 2*n:
        return 0
    return row[min(j, 2*n-j)]


def check():
    tallies = Counter()
    for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]:
        previous = half_row(1)
        harmonic = sum(pow(i, -2, p) for i in range(1, p // 3 + 1)) % p
        sign = 1 if p % 3 == 1 else -1
        for n in sorted(set(range(1, 22)) | {p, 2*p, 3*p, p*p}):
            if n*p > 5500:
                continue
            factor, unit_n = p*p, n
            while unit_n % p == 0:
                factor *= p*p
                unit_n //= p
            upper, lower, before = half_row(p*n), half_row(n), half_row(n-1)
            for j in range(2*n+1):
                delta = coefficient(upper, p*j) - coefficient(lower, j)
                digit, remainder = divmod(delta, factor)
                expected = unit_n**2 * harmonic * pow(3, -1, p) * coefficient(before, j-1) % p
                assert (remainder, digit % p) == (0, expected), (p, n, j, remainder, digit % p, expected)
                tallies['coefficients'] += 1
        r = 1
        while p**r <= 3500:
            current = half_row(p**r)
            for h in sorted(set(range(3, 17)) | {p, 2*p, p*p, 2*p*p, p**3}):
                v, unit = 0, h
                while unit % p == 0:
                    v += 1
                    unit //= p
                scale = p ** (2*r + v)
                modulus = p * scale
                delta = (moment(current, h, modulus) - moment(previous, h, modulus)) % modulus
                digit, remainder = divmod(delta, scale)
                expected = unit * pow(sign, r-1) * harmonic * pow(3, -1, p) % p
                assert (remainder, digit) == (0, expected), (p, r, h, remainder, digit, expected)
                tallies['comparisons'] += 1
                tallies['h_multiple_of_p'] += int(v > 0)
                tallies['nonzero_digit'] += int(digit != 0)
            previous = current
            r += 1
    print(dict(tallies))


if __name__ == '__main__':
    check()

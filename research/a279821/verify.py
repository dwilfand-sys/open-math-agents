"""Verify two new A279821 members using only the Python standard library."""
from math import comb, isqrt, prod


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def central(d):
    return sum(comb(d, 2*i) * comb(2*i, i) for i in range(d//2 + 1))


def coefficient(d):
    row = [1]
    for _ in range(d):
        nxt = [0] * (len(row) + 2)
        for k, a in enumerate(row):
            for offset in (0, 1, 2):
                nxt[k+offset] += a
        row = nxt
    return row[d]


def check(n, factors):
    assert n > 254677 and prod(factors) == n
    assert len(factors) == len(set(factors)) >= 2
    for p in factors:
        assert prime(p)
        value = n
        digits = []
        residues = []
        while value:
            value, d = divmod(value, p)
            assert central(d) == coefficient(d)
            digits.append(d)
            residues.append(central(d) % p)
        assert prod(residues) % p == 1
        print(n, p, digits, residues)
    assert isqrt(n)**2 != n


if __name__ == "__main__":
    check(1316632279, [31, 42472009])
    check(1793930422, [2, 37, 24242303])

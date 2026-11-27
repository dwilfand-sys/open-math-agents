"""Verify one squarefree-eligible prime for each length-three A300984 pattern."""

from itertools import product
from math import isqrt


def squarefree(n):
    return n > 0 and all(n % (q*q) for q in range(2, isqrt(n)+1))


def check(p, expected):
    assert p % 12 == 1 and all(p % q for q in range(2, isqrt(p)+1))
    word = []
    for i in (2, 3, 4):
        divisors = [(2**a*p**b, a<=1 and b<=1) for a,b in product(range(i+1), range(3))]
        s = sum(d for d, sf in divisors if sf)
        t = sum(d for d, sf in divisors if not sf)
        assert s == 3*(p+1) and squarefree(s)
        assert t == 2**(i+1)*(p*p+p+1)-(p+2)**2
        word.append("1" if squarefree(t) else "0")
    assert "".join(word) == expected


if __name__ == "__main__":
    witnesses = {"000":688729, "001":157, "010":7321, "011":109,
                 "100":2029, "101":229, "110":1237, "111":13}
    for bits, p in witnesses.items():
        check(p, bits)
        print(bits, p)

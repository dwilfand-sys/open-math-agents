"""Certify A279821 candidates using only Python's standard library.

Pass an input path (or "-" / no argument for stdin), with one positive integer
at the beginning of each non-comment line. Output JSON lines with the complete
factorization, local residues and their CRT combination. --self-test compares
the modular algorithms to direct integer trinomial coefficients.
"""

import argparse
import json
import sys
from functools import lru_cache
from math import comb, prod


def prime_powers(n):
    factors = []
    d = 2
    while d*d <= n:
        a = 0
        while n % d == 0:
            n //= d
            a += 1
        if a:
            factors.append((d, a))
        d = 3 if d == 2 else d+2
    if n > 1:
        factors.append((n, 1))
    return factors


def strip(k, p):
    assert k > 0
    v = 0
    while k % p == 0:
        k //= p
        v += 1
    return v, k


def prime_digit(n, p):
    # T(d) follows d T(d)=(2d-1)T(d-1)+3(d-1)T(d-2), where d<p.
    # The digit product follows by Frobenius: for F=x^-1+1+x, F^d has
    # no nonzero exponent divisible by p when 0<=d<p.
    ds = []
    while n:
        n, d = divmod(n, p)
        ds.append(d)
    previous = current = 1
    value = {0: 1, 1: 1}
    wanted = set(ds)
    for k in range(2, max(ds, default=0)+1):
        following = ((2*k-1)*current + 3*(k-1)*previous) * pow(k, -1, p) % p
        previous, current = current, following
        if k in wanted:
            value[k] = current
    return prod(value[d] for d in ds) % p


def direct_mod(n, p, e):
    # The k-th term of T(n) is n!/(k!^2(n-2k)!). Between consecutive
    # terms the ratio is (n-2k)(n-2k-1)/(k+1)^2. Preserve its exact
    # p-valuation and its invertible part separately, even at zero residues.
    q = p**e
    total = unit = 1
    v = 0
    for k in range(n//2):
        va, a = strip(n-2*k, p)
        vb, b = strip(n-2*k-1, p)
        vc, c = strip(k+1, p)
        v += va+vb-2*vc
        assert v >= 0
        unit = unit*a*b*pow(c*c, -1, q) % q
        if v < e:
            total = (total + unit*p**v) % q
    return total


@lru_cache(maxsize=300)
def exact_row(n):
    # Exponents -n through n, left to right.
    row = (1,)
    for _ in range(n):
        ext = (0, 0) + row + (0, 0)
        row = tuple(ext[i]+ext[i+1]+ext[i+2] for i in range(len(ext)-2))
    return row


def multiply(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return tuple(out)


class Cartier:
    """Evaluate [x^k]F^n modulo p^e with F=x^-1+1+x, including p=2,3."""

    def __init__(self, p):
        self.p = p
        diff = list(exact_row(p))
        for j in (0, p, 2*p):
            diff[j] -= 1
        assert diff[0] == diff[-1] == 0 and all(t % p == 0 for t in diff)
        self.ghost = tuple(t//p for t in diff[1:-1])
        self.polynomials = {}

    def kernel(self, d, i):
        # Extract all coefficients of F^d G^i, G=(F^p-F(x^p))/p.
        key = d, i
        if key not in self.polynomials:
            self.polynomials[key] = (exact_row(d) if i == 0 else
                                     multiply(self.kernel(d, i-1), self.ghost))
        return self.polynomials[key]

    def value(self, n, e, k=0):
        p = self.p

        @lru_cache(maxsize=None)
        def rec(t, k, prec):
            modulus = p**prec
            if k > t:
                return 0
            if t < max(40, p):
                return exact_row(t)[t+k] % modulus
            m, d = divmod(t, p)
            answer = 0
            # F^(pm+d)=Σ_i binom(m,i) p^i F^d G^i F(x^p)^(m-i).
            # Terms i>=prec vanish; every recursive exponent is smaller.
            for i in range(min(m, prec-1)+1):
                factor = p**i * comb(m, i)
                v, _ = strip(factor, p)
                if v >= prec:
                    continue
                polynomial = self.kernel(d, i)
                radius = len(polynomial)//2
                start = -radius + ((k+radius) % p)
                for j in range(start, radius+1, p):
                    weight = factor * polynomial[radius+j]
                    if not weight or weight % modulus == 0:
                        continue
                    loss, _ = strip(weight, p)
                    answer += weight * rec(m-i, abs((k-j)//p), prec-loss)
            return answer % modulus

        return rec(n, abs(k), e)


@lru_cache(maxsize=48)
def cartier(p):
    return Cartier(p)


def local(n, p, a):
    if a == 1:
        return prime_digit(n, p), "Lucas base-p digits", n
    reduced = n
    if p >= 5:
        # Pan and Sun, 2026, arXiv:2012.05121, Theorem 1.1:
        # v_p(T(pu)-T(u)) >= 2 v_p(pu). At each removed factor
        # 2*v_p(reduced)>=a, so equality modulo p^a is preserved.
        while reduced % p == 0 and 2*strip(reduced, p)[0] >= a:
            reduced //= p
    if reduced <= 2000 or p > 79:
        return direct_mod(reduced, p, a), "finite multinomial sum", reduced
    return cartier(p).value(reduced, a), "finite Cartier expansion", reduced


def certify(n):
    if n < 2:
        raise ValueError("candidate must be an integer >= 2")
    factors = prime_powers(n)
    assert prod(p**a for p, a in factors) == n
    records = []
    full = 0
    for p, a in factors:
        q = p**a
        residue, method, reduced = local(n, p, a)
        records.append(dict(p=p, exponent=a, modulus=q, residue=residue,
                            method=method, reduced_index=reduced))
        cofactor = n//q
        full = (full + residue*cofactor*pow(cofactor, -1, q)) % n
    eligible = len(factors) > 1 or factors[0][1] >= 3
    return dict(n=n, factors=records, residue=full, eligible=eligible,
                satisfies_A279821=eligible and full == 1)


def self_test():
    count = 0
    for p in (2, 3, 5, 7, 11):
        for e in range(1, 6):
            for t in (0, 1, 2, 17, 40, 53, 64, 87, 120, 183, 211):
                truth = exact_row(t)
                for k in {0, 1, 2, 9, t, t+1}:
                    expected = truth[t+k] if k <= t else 0
                    assert cartier(p).value(t, e, k) == expected % p**e
                    count += 1
                assert direct_mod(t, p, e) == truth[t] % p**e
                if e == 1:
                    assert prime_digit(t, p) == truth[t] % p
    for p, a, m in ((2, 13, 3), (3, 7, 2), (5, 5, 2), (7, 4, 2), (83, 2, 1)):
        n = p**a*m
        assert local(n, p, a)[0] == direct_mod(n, p, a)
    for n in (12, 30, 902, 1360, 2450, 3730, 21475, 74945, 82208,
              88282, 254677, 1316632279, 1793930422):
        assert certify(n)["satisfies_A279821"]
    for n in (2, 5, 25, 49):
        assert not certify(n)["eligible"]
    print(f"Passed {count} individual coefficient comparisons, five large "
          "prime-power controls, and all thirteen known positive controls.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", nargs="?", default="-")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    stream = sys.stdin if args.path == "-" else open(args.path, encoding="utf-8-sig")
    try:
        for index, line in enumerate(stream, 1):
            line = line.partition("#")[0].strip()
            if not line:
                continue
            token = line.split()[0].rstrip(",")
            try:
                n = int(token.replace(",", "").replace("_", ""))
            except ValueError:
                raise SystemExit(f"Line {index} does not start with a candidate integer.")
            print(json.dumps(certify(n), separators=(",", ":")), flush=True)
    finally:
        if stream is not sys.stdin:
            stream.close()


if __name__ == "__main__":
    main()

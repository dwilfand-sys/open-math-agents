"""Check the stronger Sun congruence T(n) = 1 mod n² on two finite sets.

Check every prime square through --limit and every named A279821 member
through that limit. Additional certified A279821 JSONL survivor files may
be supplied. For other composite n, failure mod n already implies failure
mod n²; full-interval coverage requires a complete A279821 survey.
"""

import argparse
import csv
import hashlib
import json
from math import isqrt

from check_survivors import direct_mod, local, prime_powers


MEMBERS = (12, 30, 902, 1360, 2450, 3730, 21475, 74945, 82208, 88282,
           254677, 1316632279, 1793930422)


def primes(bound):
    sieve = bytearray([1])*(bound+1)
    for p in range(2, bound+1):
        if not sieve[p]:
            continue
        yield p
        if p*p <= bound:
            sieve[p*p::p] = bytes((bound-p*p)//p+1)


def harmonic(p):
    """Return H^(2)_{floor(p/3)} mod p via factorial-scaled numerators."""
    numerator = 0
    factorial = 1
    for k in range(1, p//3+1):
        numerator = (k*k*numerator + factorial*factorial) % p
        factorial = k*factorial % p
    return numerator * pow(factorial, -2, p) % p


def square_failure(p):
    # Pan-Sun, arXiv:2012.05121, Theorem 1.1, gives
    # T(p²)=T(p) mod p⁴. Also (T(p)-1)/p² = H^(2)_{floor(p/3)}/3
    # mod p: their Bernoulli expression equals H/3 by the power-sum
    # formula, B_{p-2}(1)=0 and B_{p-2}(1-x)=-B_{p-2}(x).
    if p < 5:
        return None, p**4, direct_mod(p*p, p, 4)
    h = harmonic(p)
    if h:
        return h, p**3, 1 + p*p*(h*pow(3, -1, p) % p)
    return h, p**4, direct_mod(p, p, 4)


def member_failure(n):
    factors = prime_powers(n)
    for p, e in factors:
        residue, method, reduced_index = local(n, p, 2*e)
        if residue != 1:
            return dict(n=n, p=p, exponent=2*e, modulus=p**(2*e), residue=residue,
                        method=method, reduced_index=reduced_index)
    return dict(n=n, satisfies_n_squared=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1_800_000_000)
    parser.add_argument("--prime-table", help="optional output CSV of all prime-square obstructions")
    parser.add_argument("certificates", nargs="*", help="complete survivor JSONL files, if available")
    args = parser.parse_args()
    values = set(MEMBERS)
    for name in args.certificates:
        with open(name, encoding="utf-8-sig") as stream:
            for line in stream:
                candidate = json.loads(line)
                if candidate["satisfies_A279821"]:
                    values.add(candidate["n"])
    digest = hashlib.sha256()
    square_count = positive_h = 0
    zero_h = []
    square_passes = []
    csv_file = open(args.prime_table, "w", newline="", encoding="ascii") if args.prime_table else None
    try:
        writer = csv.writer(csv_file) if csv_file else None
        if writer:
            writer.writerow(("p", "n", "harmonic", "modulus", "residue"))
        for p in primes(isqrt(args.limit)):
            h, q, res = square_failure(p)
            if p >= 5:
                if h:
                    positive_h += 1
                else:
                    zero_h.append(p)
            if res == 1:
                square_passes.append(p*p)
            if p <= 97:
                assert direct_mod(p*p, p, 4) % q == res
                if p >= 5:
                    assert h == sum(pow(i, -2, p) for i in range(1, p//3+1)) % p
            row = (p, p*p, "" if h is None else h, q, res)
            digest.update((",".join(map(str, row))+"\n").encode("ascii"))
            if writer:
                writer.writerow(row)
            square_count += 1
    finally:
        if csv_file:
            csv_file.close()
    print(json.dumps(dict(limit=args.limit, square_count=square_count,
                          nonzero_harmonics=positive_h, zero_harmonic_primes=zero_h,
                          prime_square_passes=square_passes, table_SHA256=digest.hexdigest())))
    for n in sorted(values):
        if n <= args.limit:
            print(json.dumps(member_failure(n)))


if __name__ == "__main__":
    main()

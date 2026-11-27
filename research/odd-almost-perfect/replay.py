"""Independent replay of an ordered interval certificate, using sieve-indexed primes."""
import sys
from fractions import Fraction
from math import isqrt, prod
from functools import cache
from hashlib import sha256
from pathlib import Path

LIMIT = 140_000
prime = bytearray([1]) * (LIMIT + 1)
prime[:2] = bytes(2)
for p in range(2, isqrt(LIMIT) + 1):
    if prime[p]:
        prime[p*p::p] = bytes(1 + (LIMIT-p*p)//p)
primes = tuple(p for p in range(3, LIMIT+1) if prime[p])

@cache
def local_value(p, e):
    return sum(Fraction(1, p**j) for j in range(e+1))

def validate(k):
    path = Path(f"boxes_{k}.txt")
    labels = path.read_text(encoding="ascii").strip()
    # Prime/exponent pairs in v use a signed exponent: positive for exact,
    # negative for a lower bound. ix is the least possible next prime index.
    todo = [((), 0)]
    counts = {"A":0, "D":0}
    for tag in labels:
        v, ix = todo.pop()
        j = len(v)
        if tag == "P":
            assert j < k
            todo.append((v + ((primes[ix], -2),), ix+1))
            todo.append((v, ix+1))
        elif tag.isdigit():
            i = int(tag)
            p, e = v[i]
            assert e < 0
            todo.append((v[:i]+((p,-e),)+v[i+1:], ix))
            todo.append((v[:i]+((p,e-2),)+v[i+1:], ix))
        else:
            assert tag in counts, tag
            counts[tag] += 1
            rem = primes[ix:ix+k-j]
            assert len(rem) == k-j, (ix,k,j)
            lower = prod(local_value(p,abs(e)) for p,e in v)
            upper = prod(local_value(p,e) if e > 0 else Fraction(p,p-1) for p,e in v)
            upper *= prod(Fraction(p,p-1) for p in rem)
            min_n = prod(p**abs(e) for p,e in v) * prod(p*p for p in rem)
            if tag == "A":
                assert lower.numerator >= 2 * lower.denominator
            else:
                assert min_n * upper.numerator < (2*min_n-1) * upper.denominator
    assert not todo
    print(f"{k} primes: {counts}, {len(labels)} nodes, sha256 {sha256(path.read_bytes()).hexdigest()}", flush=True)

for k in sys.argv[1:]:
    validate(int(k))

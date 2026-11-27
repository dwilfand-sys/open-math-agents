"""Certify the four-prime case by disjoint rational interval branches."""
from fractions import Fraction as F
from functools import cache
from math import isqrt, prod
from collections import Counter
from pathlib import Path
from sys import argv

@cache
def nextprime(p):
    n = p + 2
    while any(n % d == 0 for d in range(3, isqrt(n) + 1, 2)):
        n += 2
    return n

@cache
def euler(p):
    return F(p, p - 1)

@cache
def value(p, e):
    return F((p**(e+1)-1)//(p-1), p**e)

def classify(count, certificate_path=None):
    stack = [((), 3)]
    labels = []
    leaf = Counter()
    split = Counter()
    biggest_prime = biggest_exponent = 0
    while stack:
        fixed, start = stack.pop()
        left = count - len(fixed)
        floor = []
        p = start
        for _ in range(left):
            floor.append(p)
            p = nextprime(p)
        lo = prod(value(p,e) for p,e,_ in fixed)
        hi = prod(value(p,e) if exact else euler(p) for p,e,exact in fixed) * prod(euler(p) for p in floor)
        nmin = prod(p**e for p,e,_ in fixed) * prod(p*p for p in floor)
        if 2 <= lo:
            leaf["abundant"] += 1
            labels.append("A")
            continue
        if hi + F(1,nmin) < 2:
            leaf["deficient"] += 1
            labels.append("D")
            continue
        choices = [(euler(p)/value(p,e), i) for i,(p,e,exact) in enumerate(fixed) if not exact]
        if left:
            choices.append((prod(euler(p) for p in floor), -1))
        if not choices:
            raise RuntimeError((fixed, start, lo, hi, nmin))
        _, i = max(choices)
        if i == -1:
            labels.append("P")
            stack.extend([(fixed + ((start,2,False),),nextprime(start)),(fixed,nextprime(start))])
            biggest_prime = max(biggest_prime, start)
            split["prime"] += 1
        else:
            labels.append(str(i))
            p,e,exact = fixed[i]
            stack.extend([(fixed[:i]+((p,e,True),)+fixed[i+1:],start),
                          (fixed[:i]+((p,e+2,False),)+fixed[i+1:],start)])
            biggest_exponent = max(biggest_exponent,e)
            split["exponent"] += 1
    if certificate_path is not None:
        Path(certificate_path).write_text("".join(labels) + "\n", encoding="ascii")
    return leaf, split, biggest_prime, biggest_exponent

if __name__ == "__main__":
    counts = [int(n) for n in argv[1:]] or [1, 2, 3, 4]
    for count in counts:
        print(count, classify(count, f"boxes_{count}.txt"), flush=True)

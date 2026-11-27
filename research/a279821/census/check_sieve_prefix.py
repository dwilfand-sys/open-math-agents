"""Compare the all-integer radical sieve with exact, unreduced central coefficients.

The first argument is the native sieve's candidate file beginning at n=2.
The optional second argument is the positive upper bound for the direct check.
"""

import sys
from math import prod


def factors(n):
    d = 2
    result = []
    while d*d <= n:
        e = 0
        while n % d == 0:
            n //= d
            e += 1
        if e:
            result.append((d, e))
        d = 3 if d == 2 else d+2
    if n > 1:
        result.append((n, 1))
    return result


def main():
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
    with open(sys.argv[1], encoding="utf-8-sig") as stream:
        reference = {int(line.split()[0]): line.split()[1]
                     for line in stream if line.strip() and int(line.split()[0]) <= limit}
    radical, members = {}, []
    prev, cur = 1, 1
    for n in range(2, limit+1):
        numerator = (2*n-1)*cur+3*(n-1)*prev
        nxt, rem = divmod(numerator, n)
        assert rem == 0
        prev, cur = cur, nxt
        f = factors(n)
        if len(f) == 1 and f[0][1] < 3:
            continue
        if cur % prod(p for p, e in f) == 1:
            radical[n] = "squarefree" if all(e == 1 for p, e in f) else "repeated"
            if cur % n == 1:
                members.append(n)
    assert radical == reference
    print("Direct full-integer check through", limit,
          "radical candidates", len(radical), "members", members)


if __name__ == "__main__":
    main()

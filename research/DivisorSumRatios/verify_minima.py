"""Check the least witnesses independently by the unique core form a² b³."""
from math import gcd, isqrt, prod


def primes_of(value):
    factors = {}
    d = 2
    while d*d <= value:
        while value % d == 0:
            value //= d
            factors[d] = factors.get(d, 0) + 1
        d += 1 if d == 2 else 2
    if value > 1:
        factors[value] = 1
    return factors


def explore(limit):
    factors = [primes_of(value) for value in range(1, isqrt(limit)+1)]
    factors.insert(0, {})
    instances = []
    cores = 0
    b = 1
    while b**3 <= limit:
        if all(e == 1 for e in factors[b].values()):
            for a in range(1, isqrt(limit//b**3)+1):
                core = a*a*b**3
                f = {p: 2*e for p,e in factors[a].items()}
                for p in factors[b]:
                    f[p] = f.get(p, 0)+3
                cores += 1
                total = prod((p**(e+1)-1)//(p-1) for p,e in f.items())
                sf = prod(1+p for p in f)
                if total <= sf or total % sf:
                    continue
                root = isqrt(total//sf-1)
                if (root**2+1)*sf != total or primes_of(root) == {root: 1}:
                    continue
                doubles = []
                for t in range(1,limit//core+1):
                    if gcd(t,core) != 1:
                        continue
                    ft = primes_of(t)
                    if any(e != 1 for e in ft.values()):
                        continue
                    square_sum = sf*prod(1+p for p in ft)
                    if isqrt(square_sum)**2 == square_sum:
                        doubles.append(core*t)
                instances.append((core,root,doubles))
        b += 1
    return cores, sorted(instances)


if __name__ == '__main__':
    result = explore(4_963_023_000)
    print(result)
    assert min(x[0] for x in result[1]) == 19_773_000
    assert min(n for _,_,values in result[1] for n in values) == 4_963_023_000

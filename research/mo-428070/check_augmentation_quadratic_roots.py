"""Exact checks of central-subgroup Gauss roots in five rational group algebras."""

from collections import defaultdict
from fractions import Fraction
from itertools import product


def add(a, b):
    keys = a.keys() | b.keys()
    return {x: a.get(x, 0) + b.get(x, 0) for x in keys if a.get(x, 0) + b.get(x, 0)}


def scale(c, a):
    return {x: c*y for x, y in a.items() if c*y}


def mul(a, b, compose):
    result = defaultdict(Fraction)
    for x, cx in a.items():
        for y, cy in b.items():
            result[compose(x, y)] += cx*cy
    return {x: v for x, v in result.items() if v}


def average(elements):
    return {x: Fraction(1, len(elements)) for x in elements}


def root(elements, compose, identity, prime):
    one = {identity: Fraction(1)}
    if len(elements) == 1:
        return {}
    for candidate in elements:
        if candidate == identity or any(compose(candidate, x) != compose(x, candidate) for x in elements):
            continue
        powers = [identity]
        for _ in range(prime-1):
            powers.append(compose(powers[-1], candidate))
        if len(set(powers)) == prime and compose(powers[-1], candidate) == identity:
            break
    else:
        raise AssertionError("Missing central subgroup of order p")
    gauss = {powers[a]: Fraction(1 if pow(a, (prime-1)//2, prime) == 1 else -1)
             for a in range(1, prime)}
    sign_prime = (-1)**((prime-1)//2)*prime
    e_h = average(powers)
    assert mul(gauss, e_h, compose) == {}
    assert mul(gauss, gauss, compose) == scale(sign_prime, add(one, scale(-1, e_h)))
    # Coset names are integer positions, independent of the ground representation.
    cosets, projected = [], {}
    for x in elements:
        if x in projected:
            continue
        coset = tuple(compose(x, h) for h in powers)
        for y in coset:
            projected[y] = len(cosets)
        cosets.append(coset)
    def quotient(i, j):
        return projected[compose(cosets[i][0], cosets[j][0])]
    smaller = root(list(range(len(cosets))), quotient, projected[identity], prime)
    lift = {x: c / prime for i, c in smaller.items() for x in cosets[i]}
    assert mul(lift, gauss, compose) == {} and mul(gauss, lift, compose) == {}
    result = add(gauss, lift)
    assert sum(result.values()) == 0
    assert mul(result, result, compose) == scale(sign_prime, add(one, scale(-1, average(elements))))
    return result


def check(name, group, compose, identity, prime):
    target = (-1)**((prime-1)//2)*prime
    u = add({identity: Fraction(1)}, scale(-1, average(group)))
    x = root(group, compose, identity, prime)
    for rational in (Fraction(1), Fraction(-3, 2), Fraction(5, 7)):
        y = scale(rational, x)
        assert mul(y, y, compose) == scale(rational*rational*target, u)
    print(f"{name}: order={len(group)}, c={target}, root support={len(x)}, 3 exact rational scalings")


if __name__ == "__main__":
    for n, p in ((3, 3), (5, 5), (9, 3)):
        check(f"C{n}", list(range(n)), lambda a, b: (a+b) % n, 0, p)
    check("C3 x C3", list(product(range(3), repeat=2)),
          lambda a, b: tuple((i+j) % 3 for i, j in zip(a,b)), (0,0), 3)
    def heisenberg(x, y):
        a, b, c = x
        d, e, f = y
        return ((a+d) % 3, (b+e) % 3, (c+f+a*e) % 3)
    assert heisenberg((1,0,0), (0,1,0)) != heisenberg((0,1,0), (1,0,0))
    check("Heisenberg(3)", list(product(range(3), repeat=3)), heisenberg, (0,0,0), 3)

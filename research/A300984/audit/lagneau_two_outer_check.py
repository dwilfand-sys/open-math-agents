"""Independently evaluate a small instance of the two-outer-prime sieve exactly."""
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import isqrt, prod


def prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def factor_squarefree(n):
    factors = []
    for k in range(2, isqrt(n) + 1):
        if n % k:
            continue
        n //= k
        if n % k == 0:
            return None
        factors.append(k)
    if n > 1:
        factors.append(n)
    return frozenset(factors)


def exact_case(condition):
    # Fixture for: node lagneau_two_outer.cjs 5000 19 83
    cap, small_cut, big_cut = 5000, 19, 83
    singles = {r for r in range(5, cap+1) if prime(r) and prime(2*r-1)}
    small = set(r for r in range(5, small_cut+1) if prime(r)) - singles
    rules = set()
    for d in range(7, cap+1, 6):
        if not prime(2*d-1):
            continue
        fs = factor_squarefree(d)
        if fs is None or fs & singles:
            continue
        outer = fs - small
        if len(outer) <= 1 or len(outer) == 2 and max(outer) <= big_cut:
            rules.add((fs & small, outer))

    @cache
    def p(r):
        # Legendre symbol on the discriminant -96, independently of the JS
        # congruence table modulo 24. At 7 the polynomial becomes linear.
        roots = 0
        if condition:
            roots = 1 if r == 7 else 2*int(pow(-96 % r,(r-1)//2,r) == 1)
        return Fraction(r-1-int(condition and r==7), r*(r-1)-1-roots)

    def prob_no_edge(edges):
        @cache
        def rec(candidates):
            active = [edge for edge in edges if edge <= candidates]
            if not active:
                return Fraction(1)
            v = min(set.union(*(set(edge) for edge in active)))
            near = set().union(*(edge for edge in active if v in edge)) - {v}
            return ((1-p(v))*rec(candidates-{v})
                    + p(v)*prod(1-p(j) for j in near)*rec(candidates-{v}-near))
        return rec(frozenset().union(*edges))

    total = Fraction()
    for k in range(len(small)+1):
        for chosen_tuple in combinations(sorted(small), k):
            chosen = set(chosen_tuple)
            active = [outer for ss, outer in rules if ss <= chosen]
            if frozenset() in active:
                continue
            excluded = {next(iter(e)) for e in active if len(e)==1}
            edges = {e for e in active if len(e)==2 and not e & excluded and k<=3}
            weight = prod(p(r) for r in chosen)*prod(1-p(r) for r in small-chosen)
            total += weight*prod(1-p(r) for r in excluded)*prob_no_edge(edges)
    return total*prod(1-p(r) for r in singles)


if __name__ == '__main__':
    for cond, certified in ((False,622402701943199),(True,633534338448688)):
        answer = exact_case(cond)
        upper = Fraction(certified,10**15)
        assert 0 <= upper-answer < Fraction(1,10000)
        print('squarefree F',cond,'exact finite-model density',f'{float(answer):.12f}',
              'certified excess',f'{float(upper-answer):.12f}')

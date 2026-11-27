"""Enclose the A085263 cumulative frequency constant and check the prime-square identity."""
from math import isqrt
from fractions import Fraction
from argparse import ArgumentParser


def prime_flags(n):
    flags = bytearray(b'\x01') * (n + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = bytes((n-p*p)//p+1)
    return flags


def local_mean(p):
    if p == 2:
        return Fraction(5, 2)
    # Numerators count unit nonresidues or multiples of p only, unit squares, and 0.
    half_units = p*(p-1)//2
    return ((half_units+p-1 + half_units*Fraction(p*p,p*p-2)**2
             + Fraction(p,p-1)**2)/(p*p))


def cumulative_constant(z):
    precision = 10**22
    low = upper = precision
    for p, isprime in enumerate(prime_flags(z)):
        if not isprime:
            continue
        factor = local_mean(p)
        low = low*factor.numerator//factor.denominator
        upper = -(-upper*factor.numerator//factor.denominator)
    # log tail <= 3 sum_{n>z} n^-2 <= 3/z;
    # exp(t) <= 1/(1-t) for 0<=t<1.
    return Fraction(low,precision), Fraction(upper*z,precision*(z-3))


def test_prime_squares(max_p):
    squarefree = bytearray(b'\x01')*(max_p**2+1)
    squarefree[0] = 0
    for d in range(2,max_p+1):
        squarefree[d*d::d*d] = bytes(max_p**2//(d*d))
    checked = 0
    for p,isprime in enumerate(prime_flags(max_p)):
        if p < 3 or not isprime:
            continue
        count = sum(squarefree[p*p-k*k] for k in range(1,p))
        pairs = sum(squarefree[a]*squarefree[2*p-a] for a in range(1,2*p))
        assert 2*count+1 == pairs
        checked += 1
    return checked


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--cutoff',type=int,default=1000000)
    parser.add_argument('--squares',type=int,default=2000)
    args = parser.parse_args()
    if args.cutoff < 5 or args.squares < 3:
        parser.error("Require cutoff >= 5 and squares >= 3")
    for p in [2,3,5,7,11,13,17,19,23]:
        counts=[0]*(p*p)
        for a in range(p*p):
            counts[a*a%(p*p)] += 1
        assert local_mean(p) == sum(Fraction(p*p,p*p-h)**2 for h in counts)/(p*p)
    a,b = cumulative_constant(args.cutoff)
    print('C bounds, units 10^-10:',a.numerator*10**10//a.denominator,
          -(-b.numerator*10**10//b.denominator))
    print('Prime-square identities verified:',test_prime_squares(args.squares))

"""Enclose the limiting proportions of the eight p-squared doubling patterns.

Probabilities are conditional on p = 1 mod 12 and squarefree 3(p+1).
Pass an even prime cutoff on the command line. No third-party imports.
"""
import argparse
from fractions import Fraction
from lagneau_rep_density import COEFFICIENTS, primes_through, square_divisor_roots, verify_local_counts


def compute(cutoff):
    if cutoff < 100 or cutoff%2:
        raise ValueError("Use an even cutoff of at least 100")
    precision=10**24
    low=[precision]*8
    high=low.copy()
    for q in primes_through(cutoff):
        x,y,z=counts=[square_divisor_roots(q,a) for a in COEFFICIENTS]
        if q <= 97:
            verify_local_counts(q,counts)
        d=q*q-q-1
        # The three root sets are disjoint for q>=5: the exponent
        # differences are 1 or 2 and 2^difference-1 is 1 or 3.
        for j,removed in enumerate((0,x,y,x+y,z,x+z,y+z,x+y+z)):
            low[j]=low[j]*(d-removed)//d
            high[j]=-(-high[j]*(d-removed)//d)
    for present in range(8):
        lower=upper=0
        absent=7^present
        for s in range(8):
            if s & present:
                continue
            idx=present|s
            if s.bit_count()%2:
                lower-=high[idx]
                upper-=low[idx]
            else:
                lower+=low[idx]
                upper+=high[idx]
        # A missing finite success can only have lost a required 1. A newly
        # obtained pattern must have lost at least one of its required 0s.
        left=Fraction(lower,precision)-Fraction(present.bit_count(),cutoff-1)
        right=Fraction(upper,precision)+Fraction(absent.bit_count(),cutoff-1)
        scale=10**12
        lo=left.numerator*scale//left.denominator
        hi=-(-right.numerator*scale//right.denominator)
        print(format(present,'03b')[::-1],lo,hi)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cutoff',type=int)
    compute(parser.parse_args().cutoff)

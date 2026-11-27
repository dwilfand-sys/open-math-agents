"""Independent recurrence for the three-position A300984 pattern enclosures."""
import argparse
from fractions import Fraction
from math import isqrt


def primes_up_to(n):
    odds = bytearray([1])*((n+1)//2)
    odds[0] = 0
    for p in range(3,isqrt(n)+1,2):
        if odds[p//2]:
            start=p*p//2
            odds[start::p]=bytes((len(odds)-1-start)//p+1)
    return (2*i+1 for i in range(2,len(odds)) if odds[i])


def roots(r):
    if r<=31:
        parts=[set() for _ in range(3)]
        for x in range(r*r):
            if not x%r or x==r*r-1:
                continue
            for i in range(3):
                if (2**(i+3)*(x*x+x+1)-(x+2)**2)%(r*r)==0:
                    parts[i].add(x)
        assert len(set().union(*parts))==sum(map(len,parts))
        return list(map(len,parts))
    # Quadratic reciprocity for the square classes -6, -1 and -42.
    sign = 1 if r%4==1 else -1
    two = 1 if r%8 in (1,7) else -1
    three = 1 if r%12 in (1,11) else -1
    seven = sign*(1 if r%7 in (1,2,4) else -1)
    return [1+sign*two*three,1+sign,1+sign*two*three*seven]


def check(cutoff):
    precision=10**25
    lower=[precision]+[0]*7
    upper=lower.copy()
    for r in primes_up_to(cutoff):
        counts=roots(r)
        denom=r*(r-1)-1
        l,h=[],[]
        for state in range(8):
            used=[j for j in range(3) if state & (1<<j)]
            stay=denom-sum(counts[j] for j in range(3) if j not in used)
            lo=lower[state]*stay+sum(counts[j]*lower[state^(1<<j)] for j in used)
            hi=upper[state]*stay+sum(counts[j]*upper[state^(1<<j)] for j in used)
            l.append(lo//denom)
            h.append(-(-hi//denom))
        lower,upper=l,h
    for state in range(8):
        zeros=state.bit_count()
        lo=Fraction(lower[state],precision)-Fraction(3-zeros,cutoff-1)
        hi=Fraction(upper[state],precision)+Fraction(zeros,cutoff-1)
        print(format(7^state,'03b')[::-1], lo.numerator*10**12//lo.denominator,
              -(-hi.numerator*10**12//hi.denominator))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('cutoff',type=int)
    arg=parser.parse_args()
    if arg.cutoff<32 or arg.cutoff%2:
        raise ValueError('Use an even cutoff of at least 32')
    check(arg.cutoff)

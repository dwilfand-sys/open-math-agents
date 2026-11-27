"""Rigorous enclosure of the asymptotic represented share of eligible primes."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
from lagneau_rep_density import primes_through, square_divisor_roots


def fail_bounds(low,high,k,precision,tail):
    lower=Q(0)
    upper=Q(0)
    for mask in range(1<<k):
        odd=mask.bit_count()%2
        sign=1-2*odd
        lower+=sign*Q(high[mask] if odd else low[mask],precision)
        upper+=sign*(1-tail)**mask.bit_count()*Q(low[mask] if odd else high[mask],precision)
    return max(Q(0),lower),min(Q(1),upper)


def cutoff_weight(k):
    # For k available exponents, primes extend up to X*2^(-(k-1)/2).
    d=2**((k-1)//2)
    if k%2:
        return Q(1,d),Q(1,d)
    scale=10**24
    approx=isqrt(scale**2//2)
    return Q(approx,scale*d),Q(approx+1,scale*d)


def main(R,K):
    if not 1<=K<=6 or R<100_000 or R%2:
        raise ValueError("Choose at most six witnesses and an even cutoff of at least 100,000")
    ps=primes_through(R)
    coefficients=[2**(i+1)-1 for i in range(2,K+2)]
    prec=10**24
    low=[prec]*(1<<K)
    high=low.copy()
    for q in ps:
        c=[square_divisor_roots(q,a) for a in coefficients]
        if q<=73:
            roots=[{p for p in range(1,q*q) if p%q and p!=q*q-1
                    and (a*p*p+(a-3)*(p+1))%(q*q)==0} for a in coefficients]
            assert list(map(len,roots))==c
            assert len(set().union(*roots))==sum(c)
        totals=[0]
        for value in c:
            totals.extend([a+value for a in totals])
        d=q*(q-1)-1
        for mask,removed in enumerate(totals):
            good=d-removed
            low[mask]=low[mask]*good//d
            high[mask]=-(-high[mask]*good//d)
    # Count only integers coprime to 2310 beyond R. On the k-th block of
    # length W there are phi(W) allowable classes. For its left endpoint v,
    # 1/[v(v-2)] <= (1/(v-W-2) - 1/(v-2))/W, which telescopes.
    W=2310
    Phi=480
    left=(R//W)*W
    tail=Q(2*Phi,W*(left-W-2))
    losslo=Q(0)
    losshi=Q(0)
    for k in range(1,K+1):
        lo,hi=fail_bounds(low,high,k,prec,tail)
        assert 0<=lo<=hi<=1
        weight_lo,weight_hi=cutoff_weight(k)
        next_lo,next_hi=cutoff_weight(k+1)
        losslo+=(weight_lo-next_hi)*lo
        losshi+=(weight_hi-next_lo)*hi
        print(k,'all fail',float(lo),float(hi))
    losshi+=next_hi*hi
    scale=10**15
    lowratio=(1-losshi)*scale
    highratio=(1-losslo)*scale
    print('represented fraction / 10^15',lowratio.numerator//lowratio.denominator,
          -(-highratio.numerator//highratio.denominator))


if __name__=='__main__':
    parser=ArgumentParser()
    parser.add_argument('cutoff',type=int)
    parser.add_argument('witnesses',type=int)
    args=parser.parse_args()
    main(args.cutoff,args.witnesses)

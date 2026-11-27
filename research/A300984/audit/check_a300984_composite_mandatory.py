"""Exact product-space tests for the new short and long compulsory terms."""
from fractions import Fraction as Q
from itertools import product


def active(bits,indices):
    return any(bits&(1<<i) for i in indices)


def absent(indices):
    return Q(1,2**len(set(indices)))


def run(short_on,long_linear,long_composite,extra_broad,prior_mask):
    short={4,11} if short_on else set()
    long_a={7} if long_linear else set()
    long_b={8} if long_composite else set()
    long=long_a|long_b
    assert absent(long)==absent(long_a)*absent(long_b)
    old_mass=remaining=Q()
    risks=[]
    for low in range(16):
        gate=not active(low,[0])
        rows=[]
        if active(low,[1]):
            broad={6,7,9}|({10} if extra_broad else set())
            rows.append((broad,False))
        if gate and active(low,[2]):
            rows.append(({4,5,6},True))
        if active(low,[3]):
            rows.append(({4,6},True))
        factors=[absent(long)*absent(short)]
        for leaves,is_short in rows:
            factors.append(absent(leaves)*(absent(long) if is_short else 1))
        best=min(factors)
        risks.append(1-best)
        prev=kept=0
        for high in range(256):
            bits=low|(high<<4)
            # Old event can depend on high leaf 5 only when its gate closes.
            # The mandatory short leaf 11 remains unexposed in this case.
            if (prior_mask&1 and not gate and active(bits,[5]) or
                    prior_mask&2 and active(bits,[0]) and active(bits,[2]) or
                    prior_mask&4 and active(bits,[1]) and active(bits,[3])):
                continue
            prev+=1
            if not active(bits,short|long) and all(not active(bits,leaves) for leaves,_ in rows):
                kept+=1
        assert kept<=prev*best
        old_mass+=Q(prev,4096)
        remaining+=Q(kept,4096)
    for upper in (old_mass,(old_mass+1)/2,Q(1)):
        last=loss=Q()
        for h in sorted(set(risks)):
            no_risk=Q(sum(v<h for v in risks),16)
            loss+=(h-last)*max(0,upper-no_risk)
            last=h
        assert remaining<=upper-loss


if __name__=='__main__':
    cases=0
    for switches in product((False,True),repeat=4):
        for prior_mask in range(8):
            run(*switches,prior_mask)
            cases+=1
    print(cases,'exact 12-coordinate compulsory-interval models passed.')

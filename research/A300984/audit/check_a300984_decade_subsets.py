"""Re-evaluate the certified singleton bound for any subset of high totals."""

from fractions import Fraction
from itertools import combinations
from math import factorial
from pathlib import Path
import sys
from check_a300984_published_singletons import COUNTS,reciprocal_lower
from lagneau_selberg_packing import combined_mass,coefficient_intervals,packed_mass

LEVELS = (1000,3000,10000,30000,100000,200000,300000,400000,500000,
          600000,700000,800000,1000000,1200000,1500000,2000000)


def calculate(prior,windows):
    cells=sorted(tuple(map(int,l.split())) for p in windows for l in p.read_text().splitlines())
    assert all(lo<hi and n>=0 for lo,hi,n in cells)
    assert all(b<=c for (_,b,_),(c,_,_) in zip(cells,cells[1:]))
    census={10**k:n for k,n in zip(range(10,16),COUNTS)}
    stats=coefficient_intervals(LEVELS)
    cache={}
    def maximum(hi,n):
        if (hi,n) not in cache:
            cache[hi,n]=max([reciprocal_lower(hi,n),combined_mass(hi,n,stats)]
                            +[packed_mass(hi,n,v) for v in stats.values()])
        return cache[hi,n]
    for n in range(4):
        for extra in combinations((13,14,15),n):
            points=[10**10,10**11,10**12]+[10**k for k in extra]
            mass=Fraction()
            for lo,hi in zip(points,points[1:]):
                inside=[(a,b,v) for a,b,v in cells if lo<=a<b<=hi]
                all_count=census[hi]-census[lo]
                remaining=all_count-sum(v for a,b,v in inside)
                assert remaining>=0
                fine=sum(reciprocal_lower(b,v) for a,b,v in inside)
                mass+=max(fine+maximum(hi,remaining),maximum(hi,all_count))
            mass+=sum(reciprocal_lower(b,v) for a,b,v in cells if a>=points[-1])
            ratio=Fraction(prior,10**15)/sum(mass**j/factorial(j) for j in range(6))
            print(extra,(ratio*10**12).__ceil__(),flush=True)


if __name__=='__main__':
    calculate(int(sys.argv[1]),list(map(Path,sys.argv[2:])))

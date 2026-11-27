"""Rebuild the two-selected-prime graphs and verify their integer moments."""
import argparse
import json
from math import isqrt
from pathlib import Path

import numpy as np
from lagneau_wide_replay import odd_prime_bits
from lagneau_certificate_union import read_bound


def replay(table):
    cap, small, scale = (table[key] for key in ("cap", "B", "precision"))
    prime = odd_prime_bits(2*cap)
    for row in table["rows"]:
        a, b = row["selected"]
        assert a < b <= small and a*b == max(1, a, b, a*b)
        assert all(prime(p) and not prime(2*p-1) for p in (a,b))
        assert not prime(2*a*b-1)
        multipliers = (1, a, b, a*b)
        capr = min(cap//(small+1),cap//(a*b))
        possible = np.arange(small+1+small%2,capr+1,2,dtype=np.int64)
        v = possible[prime(possible)!=0]
        for d in multipliers:
            v = v[prime(2*d*v-1)==0]
        lo, hi = scale//v, (scale+v-2)//(v-1)
        sums, squares = np.zeros_like(v), np.zeros_like(v)
        first = edges = 0
        for i, r in enumerate(v[:v.searchsorted(isqrt(cap),side="right")]):
            stop = v.searchsorted(cap//r,side="right")
            xs = v[i+1:stop]
            chosen = np.zeros(len(xs),dtype=bool)
            for d in multipliers:
                count = xs.searchsorted(cap//(r*d),side="right")
                chosen[:count] |= prime(2*d*r*xs[:count]-1)!=0
            neighbors = np.flatnonzero(chosen)+i+1
            edges += len(neighbors)
            first += int(lo[i])*int(lo[neighbors].sum())
            weights = hi[neighbors]
            sums[i] += weights.sum()
            squares[i] += (weights**2).sum()
            sums[neighbors] += hi[i]
            squares[neighbors] += hi[i]**2
        stars = sum(int(w)*(int(x)**2-int(y)) for w,x,y in zip(hi,sums,squares))
        assert (capr,len(v),edges,first,stars)==(row["vertexMax"], row["vertices"], row["edges"],
            int(row["lowerFirst"]), int(row["upperOrderedStars"])), (a,b)
        read_bound(row,scale,False)
        print("verified",a,b,edges,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("table",type=Path)
    replay(json.loads(parser.parse_args().table.read_text()))

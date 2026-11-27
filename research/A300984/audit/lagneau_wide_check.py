"""Reconstruct the wider graph by trial division and check the small fixture exactly."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import cache
from itertools import combinations
from math import isqrt, prod
from pathlib import Path
import json


@cache
def prime(n):
    return n>=2 and all(n%k for k in range(2,isqrt(n)+1))


def nonedge(edges,allowed,p):
    @cache
    def calc(remaining):
        active=[e for e in edges if e<=remaining]
        if not active:
            return F(1)
        v=min(set.union(*(set(e) for e in active)))
        near=set.union(*(set(e) for e in active if v in e))-{v}
        return ((1-p[v])*calc(remaining-{v})
                +p[v]*prod(1-p[i] for i in near)*calc(remaining-{v}-near))
    return calc(frozenset(allowed))


def check(table):
    D,B,S=table['cap'],table['B'],table['precision']
    assert D<=30000
    for row in table['rows']:
        t=row['small']
        v=[q for q in range(B+1,D//(B+1)+1) if prime(q) and not prime(2*q-1)
           and (not t or not prime(2*t*q-1))]
        edges={frozenset((r,s)) for r,s in combinations(v,2) if r*s<=D and
               (prime(2*r*s-1) or t and t*r*s<=D and prime(2*t*r*s-1))}
        u={q:(S+q-2)//(q-1) for q in v}
        finiteFirst=sum(prod(S//i for i in e) for e in edges)
        ordered=sum(prod(u[i] for i in e|f) for e in edges for f in edges if e!=f and e&f)
        assert (len(v),len(edges),finiteFirst,ordered)==(row['vertices'],row['edges'],
                     int(row['lowerFirst']),int(row['upperOrderedStars']))
        for tower in (False,True):
            p={}
            for q in v:
                roots=2*int(pow(-96%q,(q-1)//2,q)==1) if tower else 0
                p[q]=F(q-1,q*(q-1)-1-roots)
            actual=nonedge(edges,v,p)
            assert actual<=F(int(row['survivalUpper']),10**15)
    print('Verified edge sets, both moments and exact vertex-deletion probabilities for',
          len(table['rows']),'small masks')


if __name__=='__main__':
    ap=ArgumentParser()
    ap.add_argument('table',type=Path)
    check(json.loads(ap.parse_args().table.read_text()))

"""Enumerate an entire four-secant block as an unlabelled edge-colouring.

Each block chooses the three exterior double points on its A-line.
The remaining 24 missing two-secants must split into four singleton
perfect matchings. Covering the least remaining B-line at each step
enumerates every partition once.
"""
from functools import lru_cache
from itertools import product
from collections import Counter
from weight16_exact_cover import StartingCase,WORDS

def bits(entries):
    mask=0
    for e in entries:
        mask |= 1 << e
    return mask

def local_choices(case, a, emit=None):
    single=[]
    indexed_double={j:[] for j in case.double_types if a in j}
    for j in [(a,),*indexed_double]:
        available=bits(i for i,pair in enumerate(case.support_sets) if pair.isdisjoint(j))
        masks=[bits(m) for m in case.matchings(available)]
        if len(j)==1: single=masks
        else: indexed_double[j]=masks
    absent=bits(e for e,(s,t) in enumerate(case.lines)
                if a not in case.support[s] and a not in case.support[t])
    assert absent.bit_count()==36
    singles_by_edge={e:[(i,m) for i,m in enumerate(single) if m & (1<<e)] for e in range(72)}

    @lru_cache(maxsize=None)
    def partitions(residual):
        if not residual: return [()]
        bit=residual & -residual
        e=bit.bit_length()-1
        return [(i,*other) for i,m in singles_by_edge[e] if m & residual == m
                for other in partitions(residual ^ m)]

    n=0
    histogram=Counter()
    for triple in product(*indexed_double.values()):
        used=triple[0]|triple[1]|triple[2]
        if used.bit_count()!=12: continue
        choices=partitions(absent^used)
        histogram[len(choices)]+=1
        n+=len(choices)
        if emit is not None:
            for partition in choices:
                emit(a, list(zip(indexed_double,triple)), [single[i] for i in partition])
    return n,histogram

if __name__=='__main__':
    c=StartingCase(WORDS[4])
    for a in range(8):
        n,h=local_choices(c,a)
        print(a,n,'feasible triples',sum(v for k,v in h.items() if k),
              'of',sum(h.values()),'partition counts',sorted(h.items()),flush=True)


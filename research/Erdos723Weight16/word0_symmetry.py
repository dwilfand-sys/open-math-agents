"""Fixed-column exact-cover obstructions for automorphisms of Carter's cube.

If an exact cover is invariant under a permutation, a constraint fixed by the
permutation must be covered by a fixed candidate. All constraints are used
at most once. Search only over fixed candidates, imposing those necessary
conditions, and independently validate every returned witness.
"""
from collections import Counter
from itertools import combinations

from anchor_orbits import line_image, permutation_images
from scales_fixed_intersection import act
from weight16_exact_cover import StartingCase, WORDS


def compose(p, q):
    return tuple(p[x] for x in q)


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def prime_classes(group):
    identity = tuple(range(8))
    rest = set(group) - {identity}
    out = []
    while rest:
        p = min(rest)
        orbit = {compose(q, compose(p, inverse(q))) for q in group}
        assert orbit <= rest
        rest -= orbit
        power, order = p, 1
        while power != identity:
            power, order = compose(power,p), order+1
        if order in (2,3):
            out.append((order,len(orbit),p))
    return sorted(out)


def constraint_image(case,p,bl):
    order = [-1]*2280
    for (a,b),index in case.dd_col.items():
        order[index]=case.dd_col[tuple(sorted((p[a],p[b])))]
    for (b,a),index in case.ba_col.items():
        order[index]=case.ba_col[bl[b],p[a]]
    for (a,b),index in case.bb_col.items():
        order[index]=case.bb_col[tuple(sorted((bl[a],bl[b])))]
    assert sorted(order)==list(range(2280))
    return order


def solve_fixed(case,p):
    bl=line_image(case,p)
    mapping=constraint_image(case,p,bl)
    primary={i for i,j in enumerate(mapping) if i==j}
    options=[]
    histogram=Counter()
    for j,m in case.candidates():
        if act((j,m),p,bl)!=(j,m):
            continue
        histogram[len(j)]+=1
        cover=case.constraint_indices(j,m)
        if primary.intersection(cover):
            options.append((j,m,cover))
    columns={i:0 for i in primary}
    allcols=[0]*2280
    for i,(_,_,cover) in enumerate(options):
        for c in cover:
            allcols[c] |= 1<<i
            if c in primary:
                columns[c] |= 1<<i
    conflict=[0]*len(options)
    for i,(_,_,cover) in enumerate(options):
        for c in cover:
            conflict[i] |= allcols[c]
    nodes=0
    def visit(needed,available,taken):
        nonlocal nodes
        nodes+=1
        if not needed:
            return taken
        c=min(needed,key=lambda j: (columns[j] & available).bit_count())
        scan=columns[c] & available
        while scan:
            bit=scan&-scan
            scan-=bit
            i=bit.bit_length()-1
            out=visit(needed.difference(options[i][2]),available & ~conflict[i],taken+[i])
            if out is not None:
                return out
        return None
    result=visit(primary,(1<<len(options))-1,[])
    if result is not None:
        covered=Counter(c for i in result for c in options[i][2])
        assert all(covered[c]==1 for c in primary) and max(covered.values(),default=0)<=1
    return len(primary),dict(histogram),nodes,None if result is None else len(result)


if __name__=="__main__":
    case=StartingCase(WORDS[0])
    group=list(permutation_images(case))
    assert len(group)==48
    for order,size,p in prime_classes(group):
        print('order',order,'conjugacy size',size,'permutation',p,'fixed test',solve_fixed(case,p),flush=True)

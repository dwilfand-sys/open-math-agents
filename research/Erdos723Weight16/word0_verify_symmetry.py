"""Independent exact-cover search on orbits of individual nonhidden points.

This checker uses the original 2,280 incidence constraints directly. It does
not form four-secant blocks or use their precomputed compatibility tables.
"""
import argparse
from collections import Counter
from itertools import combinations
from word0_symmetry import StartingCase,WORDS,act,constraint_image,line_image,permutation_images,prime_classes


def verify(class_index,limit=None):
    c=StartingCase(WORDS[0])
    group=list(permutation_images(c))
    order,_,p=prime_classes(group)[class_index]
    bl=line_image(c,p)
    mapping=constraint_image(c,p,bl)
    # The same orbit has either all primary or all secondary constraints.
    cmap={}
    primary=set()
    for i in range(2280):
        if i in cmap: continue
        orb={i}
        v=mapping[i]
        while v!=i:
            orb.add(v);v=mapping[v]
        for x in orb: cmap[x]=i
        if i<300: primary.add(i)
    visited=set()
    options=[]
    for j,m in c.candidates():
        if not j or (j,m) in visited: continue
        orb={(j,m)}
        q=act((j,m),p,bl)
        while q!=(j,m):
            orb.add(q);q=act(q,p,bl)
        visited.update(orb)
        resources=[k for r,match in orb for k in c.constraint_indices(r,match)]
        if len(set(resources))!=len(resources): continue
        eq={cmap[x] for x in resources}
        options.append((orb,eq))
    rows={}
    for i,(_,eq) in enumerate(options):
        for x in eq: rows[x]=rows.get(x,0)|(1<<i)
    conflict=[]
    for _,eq in options:
        mask=0
        for x in eq: mask|=rows[x]
        conflict.append(mask)
    nodes=0
    complete=0
    holes=0
    def verify_inside(inside):
        nonlocal holes
        assert len(inside)==44
        used={pair for _,m in inside for pair in combinations(m,2)}
        for i,j in c.bb_col:
            if (i,j) in used: continue
            res=(1<<16)-1
            for ep in (*c.lines[i],*c.lines[j]):
                res &= ~(1<<ep)
            for rem in c.matchings(res):
                if all(tuple(sorted(pair)) not in used for pair in combinations((i,j,*rem),2)):
                    break
            else:
                holes+=1;return
        raise AssertionError('Inside solution survived the missing-partner test')
    def visit(need,allow,path):
        nonlocal nodes,complete
        nodes+=1
        if limit and nodes>limit: raise TimeoutError
        if not need:
            inside=set.union(*(options[i][0] for i in path))
            verify_inside(inside);complete+=1
            return
        # Minimum remaining domain with early termination on zero or one.
        chosen=0; best=len(options)+1
        for x in need:
            choices=rows.get(x,0)&allow
            n=choices.bit_count()
            if n<best:
                best=n;chosen=choices
                if n<2: break
        while chosen:
            bit=chosen&-chosen;chosen-=bit;i=bit.bit_length()-1
            visit(need-options[i][1],allow&~conflict[i],path+[i])
    try:
        visit(primary,(1<<len(options))-1,[])
        status='complete'
    except TimeoutError:
        status='partial'
    print('class',class_index,'order',order,'point orbits',len(options),'primary',len(primary),
          'status',status,'states',nodes,'inside',complete,'blocked',holes,flush=True)
    return status,nodes,complete


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('class_index',type=int,choices=range(6))
    ap.add_argument('--limit',type=int)
    a=ap.parse_args()
    verify(a.class_index,a.limit)

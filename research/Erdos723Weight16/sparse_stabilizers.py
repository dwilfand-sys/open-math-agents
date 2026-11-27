"""Count full graph-group orbit sizes without expanding every labelled interior."""
import argparse
from collections import Counter, defaultdict
from functools import cache
from pathlib import Path

from anchor_orbits import permutation_images, line_image
from inside_blocks import bits
from other_sparse_cases import seed_orbits
from scales_block_consistency import members
from scales_fixed_intersection import block_supports
from sparse_records import read_records
from weight16_exact_cover import StartingCase, WORDS


def count_orbits(case,records):
    group=[(p,line_image(case,p)) for p in permutation_images(case)]
    blocks=block_supports(case)
    edges=list(case.double_types)
    seeds,total=seed_orbits(case,tuple(tuple(j) for j,_ in records['0']['seed']))
    if set(records)!=set(map(str,range(len(seeds)))):
        raise ValueError('incomplete seed orbits')
    labelled=Counter()
    for i,(seed,weight) in enumerate(seeds):
        record=records[str(i)]
        if record['orbit_size']!=weight or tuple((tuple(j),tuple(m)) for j,m in record['seed'])!=seed:
            raise ValueError('inconsistent seed metadata')
        # A stabilizing permutation sends the fixed seed into one of the
        # fully observed sets of double points of this same configuration.
        by_types=defaultdict(lambda:defaultdict(list))
        for k,(p,lp) in enumerate(group):
            images=sorted((edges.index(tuple(sorted(p[a] for a in j))),bits(lp[b] for b in m)) for j,m in seed)
            types,masks=zip(*images)
            by_types[types][masks].append(k)

        @cache
        def image(k,j,m):
            p,lp=group[k]
            return tuple(sorted(p[a] for a in j)),bits(lp[b] for b in members(m))

        for term in record['inside']:
            points=set()
            for a,ii in term['blocks']:
                doubles,singles=blocks[a][ii]
                points.update(doubles)
                points.update(((a,),m) for m in singles)
            if len(points)!=44:
                raise ValueError('incorrect exterior point set')
            masks=dict((j,m) for j,m in points if len(j)==2)
            if len(masks)!=12:
                raise ValueError('incorrect number of double points')
            doubles=[masks[e] for e in edges]
            possible=[k for types,opt in by_types.items() for k in opt.get(tuple(doubles[t] for t in types),())]
            stabilizer=sum(all(image(k,j,m) in points for j,m in points) for k in possible)
            if not stabilizer or len(group)%stabilizer:
                raise ValueError('invalid stabilizer order')
            labelled[len(group)//stabilizer]+=weight
        image.cache_clear()
    if any(n%s for s,n in labelled.items()):
        raise ValueError('weighted labels do not partition into full-group orbits')
    counts={s:n//s for s,n in sorted(labelled.items())}
    print(f'{case.word:#x}, {len(group)} automorphisms, {total} seeds, {sum(labelled.values())} labelled, '
          f'{sum(counts.values())} orbits, distribution {counts}')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('case',type=int,choices=range(6))
    ap.add_argument('input',type=Path)
    args=ap.parse_args()
    count_orbits(StartingCase(WORDS[args.case]),read_records(args.input))

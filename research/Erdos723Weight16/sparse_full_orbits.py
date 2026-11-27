"""Restore all labeled interiors by the full cubic-graph automorphism group."""
import argparse
from collections import Counter
from functools import cache
from pathlib import Path

from anchor_orbits import permutation_images, line_image
from scales_block_consistency import members
from scales_fixed_intersection import block_supports
from sparse_records import read_records
from weight16_exact_cover import StartingCase, WORDS


def canonical_key(points):
    return b'\xff'.join(sorted(points))


def count_orbits(case, records):
    actions=[(p,line_image(case,p)) for p in permutation_images(case)]
    blocks=block_supports(case)

    @cache
    def point_image(g, j, mask):
        p, lines=actions[g]
        return bytes([sum(1 << p[a] for a in j), *sorted(lines[b] for b in members(mask))])

    identity=next(i for i,(p,_) in enumerate(actions) if list(p)==list(range(8)))
    seen=set()
    orbit_sizes=Counter()
    restored=0
    for row in records.values():
        restored+=row['orbit_size']*len(row['inside'])
        for terminal in row['inside']:
            points=set()
            for a,i in terminal['blocks']:
                doubles,singles=blocks[a][i]
                points.update(doubles)
                points.update(((a,),m) for m in singles)
            if len(points)!=44:
                raise ValueError('wrong number of points')
            literal=canonical_key(point_image(identity,*pt) for pt in points)
            if literal in seen:
                continue
            orbit={canonical_key(point_image(g,*pt) for pt in points) for g in range(len(actions))}
            if not seen.isdisjoint(orbit):
                raise ValueError('full group orbits overlap')
            seen.update(orbit)
            orbit_sizes[len(orbit)]+=1
    if len(seen)!=restored:
        raise ValueError(f'group images yield {len(seen)} labelings but seed weights yield {restored}')
    print(f'word {case.word:#x}: {len(actions)} automorphisms, {len(seen)} distinct labelled interiors, '
          f'{sum(orbit_sizes.values())} full-group orbits; sizes {dict(sorted(orbit_sizes.items()))}')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('case',type=int,choices=range(6))
    ap.add_argument('input',type=Path)
    args=ap.parse_args()
    count_orbits(StartingCase(WORDS[args.case]),read_records(args.input))

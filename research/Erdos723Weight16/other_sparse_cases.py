"""Inside searches and explicit missing-partner tests for other Carter words."""
import argparse
import json
from itertools import combinations, product
from pathlib import Path

from anchor_orbits import permutation_images, line_image
from inside_blocks import bits
from scales_block_consistency import BlockGraph, members
from scales_fixed_intersection import act
from scales_forced_doubles import coexist
from scales_independent_search import solve
from weight16_exact_cover import StartingCase, WORDS


def seed_orbits(case, selected):
    labels = set(selected)
    group = [(p, line_image(case,p)) for p in permutation_images(case)
             if {tuple(sorted((p[a],p[b]))) for a,b in labels} == labels]
    options = [[(j,m) for m in case.matchings(bits(i for i,s in enumerate(case.support) if set(j).isdisjoint(s)))]
               for j in selected]
    pool = {r for r in product(*options) if all(coexist(x,y) for x,y in combinations(r,2))}
    raw = len(pool)
    seeds = []
    while pool:
        rep = min(pool)
        orbit = {tuple(sorted(act(q,p,b) for q in rep)) for p,b in group}
        assert orbit <= pool
        pool -= orbit
        seeds.append((rep,len(orbit)))
    return seeds, raw


class MissingPartners:
    def __init__(self,c):
        self.case = c
        self.where = {pair:0 for pair in c.bb_col}
        self.all = 0
        for i,m in enumerate(c.matchings((1<<16)-1)):
            b = 1 << i
            self.all |= b
            for pair in combinations(m,2):
                self.where[pair] |= b

    def test(self,g,assign):
        points = set()
        for a,i in assign:
            doubles,singles = g.blocks[a][i]
            points.update(doubles)
            points.update(((a,),m) for m in singles)
        assert len(points)==44
        used = set()
        for _,m in points:
            for pair in combinations(members(m),2):
                assert pair not in used
                used.add(pair)
        mask = self.all
        for pair in used:
            mask &= ~self.where[pair]
        missing = [p for p,possible in self.where.items() if p not in used and not possible & mask]
        return mask.bit_count(),missing


if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case', type=int, choices=[0,1,2,3,5],default=1)
    ap.add_argument('--lazy', action='store_true', help='compute compatibility bitsets on demand')
    ap.add_argument('--compact', action='store_true', help='renumber each seed domain to use smaller bitsets')
    ap.add_argument('--executable',type=Path,help='use a compiled CompactClique solver on compressed domains')
    ap.add_argument('--row-cache', type=int, default=65000)
    ap.add_argument('--start',type=int,default=0)
    ap.add_argument('--stop',type=int)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    c=StartingCase(WORDS[args.case])
    selected={0:((0,1),(4,5)), 1:((4,5),(4,6),(5,6)), 2:((0,1),(4,5)),
              3:((2,4),(3,5),(4,7),(5,6)), 5:((0,1),(2,3),(4,5),(6,7))}[args.case]
    seeds, raw=seed_orbits(c,selected)
    print('word',hex(c.word),'compatible seeds',raw,'orbits',len(seeds),flush=True)
    if args.lazy or args.compact or args.executable:
        from sparse_block_domains import SparseBlockDomains
        g=SparseBlockDomains(c, cache_rows=args.row_cache)
    else:
        g=BlockGraph(c)
    check=MissingPartners(c)
    out={}
    for index,(seed,osize) in enumerate(seeds):
        if index<args.start or args.stop is not None and index>=args.stop:
            continue
        if args.compact or args.executable:
            from compact_seed_domains import CompactSeed
            compact=CompactSeed(g,seed)
            if args.executable:
                compact_vals,stats=compact.solve_compiled(args.executable)
            else:
                compact_vals,stats=solve(compact,seed)
            vals=[compact.original(val) for val in compact_vals]
        else:
            vals,stats=solve(g,seed)
        results=[]
        for val in vals:
            n,miss=check.test(g,val)
            results.append({'blocks':val,'hidden_options':n,'missing_pair':miss[0] if miss else None})
        out[index]={'seed':seed,'orbit_size':osize,'nodes_by_depth':dict(stats),'inside':results}
        print(index, 'inside',len(vals),'nodes',sum(stats.values()),'not refuted',sum(not r['missing_pair'] for r in results),flush=True)
        if args.output:
            args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')

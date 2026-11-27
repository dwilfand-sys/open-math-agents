"""Enumerate invariant inside configurations of the cube using whole A orbits."""
import argparse
import json
from collections import Counter,defaultdict
from functools import cache,lru_cache
from itertools import combinations
from pathlib import Path

from anchor_orbits import line_image,permutation_images
from inside_blocks import bits,local_choices
from other_sparse_cases import MissingPartners
from scales_block_consistency import members
from word0_symmetry import StartingCase,WORDS,prime_classes


def orbit_blocks(case,p):
    bl = line_image(case,p)
    root = []
    trans = {}
    raw = []
    for a in range(8):
        group = []
        local_choices(case,a,lambda _,d,s: group.append(tuple(sorted(tuple(d)+tuple(((a,),m) for m in s)))))
        raw.append(group)
    look = [{v:i for i,v in enumerate(group)} for group in raw]
    @cache
    def moved(point):
        j,m=point
        return tuple(sorted(p[v] for v in j)),bits(bl[v] for v in members(m))
    @cache
    def resources(point):
        j,m=point
        lines=(*j,*(8+i for i in members(m)))
        return [80*a+b for a,b in combinations(lines,2)]
    for a in range(8):
        trans[a] = [look[p[a]][tuple(sorted(map(moved,block)))] for block in raw[a]]
    todo=set(range(8))
    while todo:
        a=min(todo)
        orbit=[]
        k=a
        while k in todo:
            todo.remove(k)
            orbit.append(k)
            k=p[k]
        valid=[]
        for i,block in enumerate(raw[a]):
            t=i
            points=set()
            assignment=[]
            for x in orbit:
                assignment.append((x,t))
                points.update(raw[x][t])
                t=trans[x][t]
            if t!=i: continue
            res=set()
            for pt in points:
                rr=resources(pt)
                if any(r in res for r in rr): break
                res.update(rr)
            else:
                valid.append((tuple(assignment),tuple(sorted(points))))
        root.append((tuple(orbit),valid))
    return root,resources,raw


def solve_class(c,p,first_limit=None,report_every=0):
    families,resources,raw=orbit_blocks(c,p)
    print('A orbits and feasible compound options',[(o,len(v)) for o,v in families],flush=True)
    full=[(1<<len(opts))-1 for orb,opts in families]
    by_pair=[]
    by_point=[]
    for orb,opts in families:
        bitwidth=(len(opts)+7)//8
        idx=defaultdict(lambda:bytearray(bitwidth))
        labels=defaultdict(lambda:bytearray(bitwidth))
        for i,(_,points) in enumerate(opts):
            b,v=divmod(i,8)
            flag=1<<v
            for point in points:
                labels[point][b] |= flag
                for r in resources(point): idx[r][b] |= flag
        by_pair.append({k:int.from_bytes(v,'little') for k,v in idx.items()})
        by_point.append({k:int.from_bytes(v,'little') for k,v in labels.items()})
    @cache
    def clashes(k,pt):
        mask=0
        for r in resources(pt): mask |= by_pair[k].get(r,0)
        return mask
    @lru_cache(maxsize=120000)
    def compatible(a,i,b):
        mask=full[b]
        dest=families[b][0]
        forbidden=0
        for pt in families[a][1][i][1]:
            if any(k in dest for k in pt[0]):
                mask &= by_point[b].get(pt,0)
            else:
                forbidden |= clashes(b,pt)
        return mask & ~forbidden
    count=Counter()
    examples=[]
    def run(dom,path):
        count[len(path)]+=1
        if not dom:
            examples.append(tuple(sorted(item for a,i in path for item in families[a][1][i][0])))
            return
        a=min(dom,key=lambda i:dom[i].bit_count())
        for offset,i in enumerate(members(dom[a])):
            if not path:
                if first_limit is not None and offset>=first_limit: break
                if report_every and offset%report_every == 0:
                    print('first options',offset,'/',dom[a].bit_count(),'inside',len(examples),'states',sum(count.values()),flush=True)
            new={}
            for b,v in dom.items():
                if b==a: continue
                d=v&compatible(a,i,b)
                if not d: break
                new[b]=d
            else:
                run(new,path+[(a,i)])
    run(dict(enumerate(full)),[])
    print('visited',dict(sorted(count.items())),'complete inside',len(examples),flush=True)
    if not examples: return [],count
    # Use the original inside-block ordering to run the earlier independent
    # missing-partner test and verify all 44 point and row-pair incidences.
    class RawBlocks: pass
    g=RawBlocks()
    g.blocks=[[(tuple((j,m) for j,m in points if len(j)==2),
                tuple(m for j,m in points if len(j)==1)) for points in group] for group in raw]
    checker=MissingPartners(c)
    result=[]
    for e in examples:
        n,miss=checker.test(g,e)
        result.append({'blocks':e,'hidden_options':n,'missing_pair':miss[0] if miss else None})
    print('solutions passing missing-partner test',sum(not x['missing_pair'] for x in result),flush=True)
    return result,count


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('class_index',type=int,choices=range(6))
    ap.add_argument('--first-limit',type=int)
    ap.add_argument('--report-every',type=int,default=0)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    c=StartingCase(WORDS[0])
    order,size,p=prime_classes(list(permutation_images(c)))[args.class_index]
    print('class',args.class_index,p,'order',order,'class size',size,flush=True)
    sols,counts=solve_class(c,p,args.first_limit,args.report_every)
    if args.output:
        args.output.write_text(json.dumps(dict(word=hex(c.word),permutation=p,first_limit=args.first_limit,
                         nodes=dict(counts),inside=sols),separators=(',',':'))+'\n',encoding='utf8')

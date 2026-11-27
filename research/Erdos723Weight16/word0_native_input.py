"""Serialize the cube A blocks and seed orbits for the independent C# traversal."""
import argparse
from array import array
from pathlib import Path
from other_sparse_cases import seed_orbits
from inside_blocks import local_choices,bits
from scales_block_consistency import members
from weight16_exact_cover import StartingCase,WORDS


def write(path, case_index=0):
    c=StartingCase(WORDS[case_index])
    pts={}; groups=[]
    def identify(v):
        if v not in pts: pts[v]=len(pts)
        return pts[v]
    for a in range(8):
        blocks=[]
        def add(_,ds,ss):
            blocks.append([identify(p) for p in ds]+[identify(((a,),m)) for m in ss])
        local_choices(c,a,add)
        groups.append(blocks)
    selected = {0: ((0,1),(4,5)), 5: ((0,1),(2,3),(4,5),(6,7))}
    seeds,_=seed_orbits(c,selected[case_index])
    data=array('i',[73002,len(pts)])
    for j,m in pts:
        B=list(members(m))
        data.extend([len(j),*j,len(B),*B])
    for group in groups:
        data.append(len(group))
        for block in group: data.extend(block)
    data.append(len(seeds))
    for seed,size in seeds:
        data.extend([size,len(seed),*(pts[(j,bits(m))] for j,m in seed)])
    with path.open('wb') as f: data.tofile(f)
    print(len(pts),'possible nonhidden points,',sum(map(len,groups)),'row blocks,',len(seeds),'seeds',flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('output',type=Path)
    ap.add_argument('--case',type=int,choices=(0,5),default=0)
    args=ap.parse_args()
    write(args.output,args.case)

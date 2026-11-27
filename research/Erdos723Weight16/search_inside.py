"""Bounded Algorithm X search with exact and at-most-one intersection constraints.

Only the empty-type outside points meeting a selected two-secant are kept.
For all candidates the B--B pairs are at most once; for the chosen line they
are exactly once. A full sparse weight-16 configuration would give a solution
to this relaxation. A node limit yields UNKNOWN, never an infeasibility claim.
"""
import argparse
import time
from weight16_exact_cover import StartingCase, WORDS

def instance(case,anchor):
    catalog=[]
    for rows, matching in case.candidates():
        if not rows and anchor not in matching:
            continue
        catalog.append(case.constraint_indices(rows,matching))
    primary=set(range(300))
    primary.update(col for pair,col in case.bb_col.items() if anchor in pair)
    assert len(primary) == 355
    return catalog,sorted(primary)

def search(rows,primary,limit,deadline):
    width=2280
    byte_width=(len(rows)+7)//8
    raw=[bytearray(byte_width) for _ in range(width)]
    for r,row in enumerate(rows):
        for c in row:
            raw[c][r//8] |= 1 << (r%8)
    bycol=[int.from_bytes(v,'little') for v in raw]
    cols={c: i for i,c in enumerate(primary)}
    primary_cover=[]
    conflicts=[]
    for row in rows:
        covered=0
        excluded=0
        for col in row:
            excluded |= bycol[col]
            if col in cols:
                covered |= 1 << cols[col]
        primary_cover.append(covered)
        conflicts.append(excluded)
    relevant=[bycol[c] for c in primary]
    nodes=0
    maxdepth=0
    chosen=[]
    def visit(allowed,needed):
        nonlocal nodes,maxdepth
        nodes+=1
        if nodes>limit or nodes%1024==0 and time.monotonic()>=deadline:
            raise TimeoutError
        maxdepth=max(maxdepth,len(chosen))
        if not needed: return True
        scan=needed
        best_count=len(rows)+1
        best=0
        while scan:
            bit=scan & -scan
            opts=allowed & relevant[bit.bit_length()-1]
            num=opts.bit_count()
            if num < best_count:
                best_count,best=num,opts
                if not num: return False
                if num==1: break
            scan ^= bit
        while best:
            branch=best & -best
            row=branch.bit_length()-1
            chosen.append(row)
            if visit(allowed & ~conflicts[row],needed & ~primary_cover[row]): return True
            chosen.pop()
            best^=branch
        return False
    try:
        found=visit((1<<len(rows))-1,(1<<len(primary))-1)
        result='SAT' if found else 'UNSAT'
    except TimeoutError:
        result='UNKNOWN'
    if result=='SAT':
        counts=[0]*width
        for i in chosen:
            for j in rows[i]: counts[j]+=1
        assert all(counts[j]==1 for j in primary) and max(counts)==1
    return result,nodes,maxdepth,chosen if result=='SAT' else []

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--case',type=int,default=4,choices=range(6))
    ap.add_argument('--anchor',type=int,default=0,choices=range(72))
    ap.add_argument('--nodes',type=int,default=250_000)
    ap.add_argument('--seconds',type=float,default=45.)
    args=ap.parse_args()
    case=StartingCase(WORDS[args.case]);start=time.monotonic()
    rows,primary=instance(case,args.anchor)
    print(f'word={case.word:#x} B={args.anchor} candidate rows={len(rows)} primary={len(primary)}',flush=True)
    result,nodes,depth,witness=search(rows,primary,args.nodes,time.monotonic()+args.seconds)
    print(f'{result}: {nodes} nodes, max depth {depth}, elapsed {time.monotonic()-start:.2f}s',flush=True)
    if witness: print(witness)


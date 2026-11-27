"""Search the sparse Carter instance by grouping all seven points of an A-line.

For each shared double point the two endpoint blocks must choose the same
matching. Its B-pair intersections are charged to the smaller endpoint.
This makes each chosen block a single option in Algorithm X. Rows for empty
points are retained only if they meet the selected two-secant.
"""
import argparse
import time
from collections import defaultdict
from itertools import combinations
from functools import cache
from inside_blocks import bits,local_choices
from weight16_exact_cover import StartingCase,WORDS

def set_bits(x):
    while x:
        b=x&-x
        yield b.bit_length()-1
        x-=b

def prepare(case,anchor):
    rows=[]
    @cache
    def resources(m):
        return tuple(case.bb_col[p]-300 for p in combinations(set_bits(m),2))
    def append(a, doubles, singles):
        bb=[]
        for m in singles: bb.extend(resources(m))
        for j,m in doubles:
            if j[0]==a: bb.extend(resources(m))
        assert len(bb)==len(set(bb))
        rows.append((a,tuple(bb),tuple(doubles)))
    for a in range(8):
        local_choices(case,a,append)
    for matching in case.matchings((1<<16)-1):
        if anchor in matching:
            rows.append((8,resources(bits(matching)),()))
    n=len(rows)
    bytewidth=(n+7)//8
    bb_index=[bytearray(bytewidth) for _ in range(1980)]
    groups=[bytearray(bytewidth) for _ in range(9)]
    labels=defaultdict(dict)
    for idx,(a,bb,dbl) in enumerate(rows):
        byte,bit=idx//8,1<<(idx%8)
        groups[a][byte]|=bit
        for b in bb: bb_index[b][byte]|=bit
        for j,m in dbl:
            labels[j].setdefault(m,bytearray(bytewidth))[byte]|=bit
    bb_index=[int.from_bytes(z,'little') for z in bb_index]
    group_masks=[int.from_bytes(z,'little') for z in groups]
    labels={j:{m:int.from_bytes(v,'little') for m,v in opts.items()} for j,opts in labels.items()}
    cols={b:i+8 for i,b in enumerate(case.bb_col[p]-300 for p in case.bb_col if anchor in p)}
    assert len(cols)==55
    exact=group_masks[:8]+[bb_index[b] for b in cols]
    @cache
    def conflicts(i):
        a,bb,dbl=rows[i]
        out=0 if a==8 else group_masks[a]
        for b in bb: out|=bb_index[b]
        for j,m in dbl:
            other=j[1] if a==j[0] else j[0]
            out|=group_masks[other] & ~labels[j][m]
        return out
    primary=[]
    for a,bb,dbl in rows:
        h=0 if a==8 else 1<<a
        for b in bb:
            if b in cols: h|=1<<cols[b]
        primary.append(h)
    return rows,exact,conflicts,primary

def run(case,anchor,node_limit,seconds):
    rows,exact,conflicts,primary=prepare(case,anchor)
    print(f'{len(rows)} compound options, {len(exact)} exact constraints, 1925 secondary B-pair constraints',flush=True)
    chosen=[]
    states=0
    deepest=0
    deadline=time.monotonic()+seconds
    def visit(available,needed):
        nonlocal states,deepest
        states+=1
        if states>node_limit or states%1024==0 and time.monotonic()>deadline: raise TimeoutError
        deepest=max(deepest,len(chosen))
        if not needed: return True
        best_size=len(rows)+1; opts=0
        for c in set_bits(needed):
            v=exact[c]&available
            sz=v.bit_count()
            if sz<best_size:
                opts,best_size=v,sz
                if sz==0:return False
                if sz==1:break
        for i in set_bits(opts):
            chosen.append(i)
            if visit(available&~conflicts(i),needed&~primary[i]):return True
            chosen.pop()
        return False
    try: result='SAT' if visit((1<<len(rows))-1,(1<<len(exact))-1) else 'UNSAT'
    except TimeoutError:result='UNKNOWN'
    if result=='SAT':
        seen=0; active=(1<<len(rows))-1
        for i in chosen:
            assert active & (1<<i) and not (seen&primary[i])
            seen|=primary[i];active&=~conflicts(i)
        assert seen==(1<<len(exact))-1
    return result,states,deepest

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--case',type=int,default=4,choices=range(6))
    ap.add_argument('--anchor',type=int,default=6,choices=range(72))
    ap.add_argument('--nodes',type=int,default=1000000)
    ap.add_argument('--seconds',type=float,default=50.)
    args=ap.parse_args()
    start=time.monotonic()
    print(run(StartingCase(WORDS[args.case]),args.anchor,args.nodes,args.seconds),f'{time.monotonic()-start:.2f}s')


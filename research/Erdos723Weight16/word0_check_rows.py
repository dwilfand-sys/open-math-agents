"""Validate and summarize every unrestricted cube inside tuple from a traversal."""
import argparse
import hashlib
import json
from collections import Counter
from itertools import combinations
from pathlib import Path

from inside_blocks import bits,local_choices
from other_sparse_cases import seed_orbits,MissingPartners
from scales_block_consistency import members
from weight16_exact_cover import StartingCase,WORDS


def blocked_directly(c,used,pair):
    i,j=pair
    if pair in used or pair not in c.bb_col: return False
    residual=(1<<16)-1
    for v in (*c.lines[i],*c.lines[j]): residual &= ~(1<<v)
    for matching in c.matchings(residual):
        if all(tuple(sorted(p)) not in used for p in combinations((i,j,*matching),2)):
            return False
    return True


def check_dir(root,out,allow_partial,witnesses):
    c=StartingCase(WORDS[0])
    seeds,raw=seed_orbits(c,((0,1),(4,5)))
    idx=[]
    for a in range(8):
        group=[]
        def record(_,ds,ss):
            group.append(tuple((j,tuple(members(m))) for j,m in ds)
                         +tuple(((a,),tuple(members(m))) for m in ss))
        local_choices(c,a,record)
        idx.append(group)
    hidden=MissingPartners(c)
    result=[]
    catalogue=['seed\tA0\tA1\tA2\tA3\tA4\tA5\tA6\tA7\tB1\tB2\n']
    for si,(seed,osize) in enumerate(seeds):
        path=root/f'cube-seed-{si:02d}.txt'
        if not path.exists():
            if allow_partial:continue
            raise FileNotFoundError(path)
        rows=sorted(tuple(map(int,line.split(','))) for line in path.read_text().splitlines())
        assert len(rows)==len(set(rows))
        digest=hashlib.sha256();count=Counter();unknown=[]
        for row in rows:
            points=set(pt for a,i in enumerate(row) for pt in idx[a][i])
            assert len(points)==44 and set(seed)<=points
            cover=Counter(x for j,m in points for x in c.constraint_indices(j,m))
            assert all(cover[x]==1 for x in range(300)) and max(cover.values())==1
            used={pair for _,m in points for pair in combinations(m,2)}
            available=hidden.all
            for pair in used:available &= ~hidden.where[pair]
            missing=next((pair for pair,x in hidden.where.items() if pair not in used and not x&available),None)
            if missing is not None:
                assert blocked_directly(c,used,missing)
                count['missing_pair']+=1
            else:
                unknown.append(row)
            digest.update((','.join(map(str,row))+':'+str(missing)+'\n').encode('ascii'))
            if missing is not None:
                catalogue.append('\t'.join(map(str,(si,*row,*missing)))+'\n')
        result.append(dict(index=si,seed=seed,orbit_size=osize,inside=len(rows),
                           missing_pair=count['missing_pair'],surviving=unknown,
                           certificate_sha256=digest.hexdigest()))
        print('seed',si,'weight',osize,'inside',len(rows),'surviving',len(unknown),flush=True)
    print('TOTAL seeds',len(result),'raw cover',sum(x['orbit_size'] for x in result),'of',raw,
          'inside',sum(x['inside'] for x in result),'surviving',sum(len(x['surviving']) for x in result),flush=True)
    if out:
        out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    if witnesses:
        witnesses.write_text(''.join(catalogue),encoding='utf8',newline='\n')


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--witnesses',type=Path)
    ap.add_argument('--allow-partial',action='store_true')
    a=ap.parse_args();check_dir(a.directory,a.output,a.allow_partial,a.witnesses)

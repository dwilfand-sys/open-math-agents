"""Restore all labelled cube configurations and independently classify stabilizers."""
from collections import Counter
from functools import cache
from pathlib import Path
import argparse,json
from inside_blocks import bits,local_choices
from scales_block_consistency import members
from anchor_orbits import permutation_images,line_image
from weight16_exact_cover import StartingCase,WORDS


def run(summary,certs):
    c=StartingCase(WORDS[0])
    group=list(permutation_images(c))
    row_action=[line_image(c,p) for p in group]
    ids={};points=[];blocks=[];index=[]
    def identify(j,m):
        if (j,m) not in ids:
            ids[j,m]=len(points);points.append((j,m))
        return ids[j,m]
    for a in range(8):
        opts=[]
        def emit(_,ds,ss):
            opts.append(tuple(sorted([identify(j,m) for j,m in ds]+[identify((a,),m) for m in ss])))
        local_choices(c,a,emit)
        blocks.append(opts);index.append({v:i for i,v in enumerate(opts)})
    moved=[]
    for p,b in zip(group,row_action):
        moved.append([ids[tuple(sorted(p[a] for a in j)),bits(b[i] for i in members(m))] for j,m in points])
    @cache
    def move_block(t,a,i):
        return index[group[t][a]][tuple(sorted(moved[t][q] for q in blocks[a][i]))]
    def move(t,v):
        dst=[0]*8
        for a,i in enumerate(v):dst[group[t][a]]=move_block(t,a,i)
        return tuple(dst)
    all_inside=set();hist=Counter()
    rows=[list(map(int,line.split())) for line in certs.read_text().splitlines()[1:]]
    for data in rows:
        v=tuple(data[1:9])
        if v in all_inside:continue
        orb={move(t,v) for t in range(48)}
        assert not (all_inside&orb)
        all_inside.update(orb)
        hist[48//len(orb)]+=1
    expected=sum(s['orbit_size']*s['inside'] for s in json.loads(summary.read_text()))
    assert len(all_inside)==expected
    assert hist[2]==11 and hist[3]==6 and set(hist)<={1,2,3}
    print('Restored',len(all_inside),'labelled inside configurations in',sum(hist.values()),
          'cube orbits; orbit counts by stabilizer order',dict(sorted(hist.items())),flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('summary',type=Path)
    ap.add_argument('certificates',type=Path)
    a=ap.parse_args();run(a.summary,a.certificates)

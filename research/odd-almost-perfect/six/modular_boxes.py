"""Exploratory exact interval search, with bounded prime intervals and modular obstructions."""
from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, prod
from pathlib import Path
from sys import argv
from time import monotonic
import json

LIMIT = 200_000
mask = bytearray([1]) * (LIMIT+1)
mask[:2] = bytes(2)
for p in range(2,isqrt(LIMIT)+1):
    if mask[p]:
        mask[p*p::p] = bytes(1+(LIMIT-p*p)//p)
primes = [p for p in range(3,LIMIT+1,2) if mask[p]]
def up(n):
    if n <= primes[-1]:
        return primes[bisect_left(primes,n)]
    return n | 1

def down(n):
    if n <= LIMIT:
        i = bisect_right(primes,n)
        return primes[i-1] if i else 1
    return n if n%2 else n-1

@lru_cache(maxsize=80000)
def ratio(p,e):
    power=p**e
    return (p*power-1)//(p-1),power

@lru_cache(maxsize=8000)
def residues(modulus, r, e, exact):
    power = 1
    total = 1
    for _ in range(e):
        power = power*r % modulus
        total = (total+power)%modulus
    if exact:
        return frozenset((total,))
    seen = set()
    values = set()
    while (power,total) not in seen:
        seen.add((power,total))
        values.add(total)
        power = power*r % modulus
        total = (total+power)%modulus
        power = power*r % modulus
        total = (total+power)%modulus
    return frozenset(values)

@lru_cache(maxsize=80000)
def possible_residues(modulus, lo, hi, e, exact):
    if lo == hi:
        return residues(modulus,lo%modulus,e,exact)
    if hi and hi-lo < modulus:
        rs = {x%modulus for x in range(lo,hi+1,2)}
    else:
        rs = range(modulus) if modulus%2 else range(1,modulus,2)
    return frozenset().union(*(residues(modulus,r,e,exact) for r in rs))

def mod_exclusion(box):
    fixed = [lo for lo,hi,_,_ in box if lo==hi]
    for m,goal in [(3,-1),(5,-1),(7,-1),(11,-1),(13,-1),(16,1)]:
        if m != 16 and m not in fixed:
            continue
        want = goal%m
        values = {1}
        for lo,hi,e,x in box:
            choices = possible_residues(m,lo,hi,e,x)
            values = {a*b%m for a in values for b in choices}
            if not values or values=={0}:
                break
        if want not in values:
            return True
    for lo,hi,e,exact in box:
        if lo==hi and exact:
            s = (lo**(e+1)-1)//(lo-1)
            if any(s%q==0 for q in fixed):
                return True
    return False

def normalize(box):
    tmp=[]
    b=3
    for lo,hi,e,x in box:
        lo=up(max(lo,b)); b=lo+2
        if hi and lo>hi:
            return None
        tmp.append([lo,hi,e,x])
    ceiling=0
    for row in reversed(tmp):
        lo,hi,e,x=row
        if ceiling:
            hi=min(hi,ceiling) if hi else ceiling
        if hi:
            hi=down(hi)
            if lo>hi:
                return None
            ceiling=hi-2
        row[1]=hi
    return tuple(tuple(row) for row in tmp)

def extension_bounds(box):
    for _ in range(3):
        rows=[]
        ln=ld=un=ud=1
        for lo,hi,e,x in box:
            a,b=ratio(hi,e) if hi else (1,1)
            c,d=ratio(lo,e) if x else (lo,lo-1)
            rows.append((a,b,c,d))
            ln*=a;ld*=b;un*=c;ud*=d
        contracted=[]
        for (lo,hi,e,x),(a,b,c,d) in zip(box,rows):
            lower_num,lower_den=ln//a,ld//b
            gap=2*lower_den-lower_num
            if gap<=0:
                return None
            new_lo=max(lo,2*lower_den//gap)
            upper_num,upper_den=un//c,ud//d
            upper_gap=2*upper_den-upper_num
            if upper_gap>0:
                cap=(2*upper_den-1)//upper_gap
                new_hi=min(hi,cap) if hi else cap
                if new_lo>new_hi:
                    return None
            else:
                new_hi=hi
            contracted.append((new_lo,new_hi,e,x))
        new=normalize(contracted)
        if new is None:
            return None
        if new==box:
            return new
        box=new
    return box

ALLOWED={1:(0,6),3:(0,4),5:(0,2),7:(0,2,4,6)}

BAD_PRODUCT=prod(q for q in primes if q<=3000 and q%8 in (3,5))

@lru_cache(maxsize=120000)
def factor_sieve_ok(p,e):
    v=ratio(p,e)[0]
    return v%8 in (1,7) and gcd(v,BAD_PRODUCT)==1

def factor_sieve_bounds(box):
    rows=[]
    for lo,hi,e,x in box:
        if x:
            while (not hi or lo<=hi) and not factor_sieve_ok(lo,e):
                lo=up(lo+2)
            while hi and lo<=hi and not factor_sieve_ok(hi,e):
                hi=down(hi-2)
            if hi and lo>hi:
                return None
        if lo==hi:
            while not factor_sieve_ok(lo,e):
                e+=2
        rows.append((lo,hi,e,x))
    return normalize(rows)

def character_bounds(box):
    rows=[]
    for lo,hi,e,x in box:
        if x:
            while e%8 not in ALLOWED[lo%8]:
                lo=up(lo+2)
            while hi and lo<=hi and e%8 not in ALLOWED[hi%8]:
                hi=down(hi-2)
            if hi and lo>hi:
                return None
        if lo==hi:
            while e%8 not in ALLOWED[lo%8]:
                e+=2
        rows.append((lo,hi,e,x))
    return normalize(rows)

def prove(k,limit_secs=60,max_nodes=1_000_000_000,checkpoint=None,extension=False,character=False,sieve=False):
    base=normalize([(3,0,2,False)]*k)
    queue=[base]
    stats=Counter()
    maxp=maxe=0
    if checkpoint and Path(checkpoint).exists():
        data=json.loads(Path(checkpoint).read_text(encoding="ascii"))
        assert data["version"]==(5 if sieve else 4 if character else 3 if extension else 2) and data["primes"]==k
        usual={2:[False,False,False],3:[True,False,False],4:[True,True,False],5:[True,False,True]}
        assert data.get("modes",usual[data["version"]])==[extension,character,sieve]
        queue=[tuple(tuple(row) for row in box) for box in data["queue"]]
        stats.update(data["stats"])
        maxp=data["maxp"]; maxe=data["maxe"]
    def snapshot():
        if checkpoint:
            payload=dict(version=5 if sieve else 4 if character else 3 if extension else 2,primes=k,queue=queue,stats=stats,maxp=maxp,maxe=maxe,modes=[extension,character,sieve])
            temp=Path(str(checkpoint)+".new")
            temp.write_text(json.dumps(payload),encoding="ascii")
            temp.replace(checkpoint)
    tic=monotonic()
    while queue:
        if stats["nodes"] and stats["nodes"]%262144==0:
            snapshot()
            if checkpoint:
                print("Checkpoint",stats["nodes"],"nodes; outstanding boxes",len(queue),flush=True)
        if stats['nodes']%1024==0 and (monotonic()-tic >= limit_secs or stats['nodes']>=max_nodes):
            snapshot()
            return False,stats,len(queue),maxp,maxe,round(monotonic()-tic,2)
        stats['nodes']+=1
        box=queue.pop()
        if sieve:
            box=factor_sieve_bounds(box)
            if box is None:
                stats["factor sieve"]+=1; continue
        if character:
            box=character_bounds(box)
            if box is None:
                stats["character"]+=1; continue
        if extension:
            box=extension_bounds(box)
            if box is None:
                stats["extension"]+=1; continue
        ln=ld=1
        for lo,hi,e,x in box:
            if hi:
                a,b=ratio(hi,e)
                ln*=a;ld*=b
        if ln>=2*ld:
            stats['abundant']+=1; continue
        un=ud=nmin=1
        for lo,hi,e,x in box:
            a,b=ratio(lo,e)
            nmin*=b
            un*=a if x else lo
            ud*=b if x else lo-1
        if un*nmin+ud<2*ud*nmin:
            stats['deficient']+=1; continue
        if mod_exclusion(box):
            stats['modular']+=1; continue
        choices=[]
        for i,(lo,hi,e,x) in enumerate(box):
            if lo!=hi:
                choices.append(((1/(lo-1) - (1/(hi-1) if hi else 0)),True,i))
            if not x:
                choices.append((lo**(-e-1),False,i))
        if not choices:
            raise ValueError(('unclassified',box))
        _,pb,i=max(choices)
        lo,hi,e,x=box[i]
        if pb:
            if lo<19 or hi and hi-lo<8:
                cut=lo
            else:
                cut=(2*lo*hi//(lo+hi)) if hi else 2*lo
                if hi:
                    cut=min(cut,hi-1)
            maxp=max(maxp,cut)
            regions=[(lo,cut,e,x),(cut+1,hi,e,x)]
            stats['prime split']+=1
        else:
            maxe=max(maxe,e)
            regions=[(lo,hi,e,True),(lo,hi,e+2,False)]
            stats['exponent split']+=1
        for item in regions:
            child=normalize(box[:i]+(item,)+box[i+1:])
            if child:
                queue.append(child)
    snapshot()
    return True,stats,0,maxp,maxe,round(monotonic()-tic,2)

if __name__ == '__main__':
    for k in [int(x) for x in argv[1:]] or [4,5,6]:
        print(k, prove(k), flush=True)

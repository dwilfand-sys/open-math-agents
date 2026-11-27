"""Read the generated Lean branch layout and compare each leaf to the replayed data."""
from collections import Counter
from fractions import Fraction as F
from math import isqrt, prod
from pathlib import Path
import re

ROOT = Path(__file__).parent
text = (ROOT / "FourPrimeExclusion.lean").read_text(encoding="utf8")
text = text[text.index("  by_cases h : p 0 = 3"):text.index("/-- No odd almost-perfect square")]
decision = re.compile(r"by_cases h : ([pe]) ([0-3]) = (\d+)")
coord = re.compile(r"⟨(\d+), (\d+), (true|false), (true|false)⟩")
path_stack = {}
from_source = {}
for line in text.splitlines():
    s = line.lstrip()
    col = len(line)-len(s)
    if s.startswith("· "):
        for depth in [k for k in path_stack if k > col]:
            del path_stack[depth]
        if col in path_stack:
            path_stack[col][3] += 1
            assert path_stack[col][3] in (0,1)
        s = s[2:]
        col += 2
    case = decision.fullmatch(s)
    if case:
        what, idx, val = case.groups()
        path_stack[col] = [what, int(idx), int(val), -1]
    if "apply bad ![" in s:
        branch = tuple((w,i,v,side==0) for _,(w,i,v,side) in sorted(path_stack.items()))
        box = tuple((int(p),int(e),pp=="true",ee=="true") for p,e,pp,ee in coord.findall(s))
        assert len(box)==4 and branch not in from_source
        from_source[branch] = box

primes = [p for p in range(3, 300,2) if all(p%q for q in range(2,isqrt(p)+1))]
tree = (ROOT / "boxes_4.txt").read_text(encoding="ascii").strip()
pending = [((),0,())]
counts = Counter()
for tag in tree:
    fixed, ix, path = pending.pop()
    if tag == "P":
        j = len(fixed)
        label = ("p", j, primes[ix])
        pending.append((fixed+((primes[ix],2,True,False),),ix+1,path+(label+(True,),)))
        pending.append((fixed,ix+1,path+(label+(False,),)))
    elif tag.isdigit():
        i = int(tag)
        p,e,_,_ = fixed[i]
        label = ("e", i, e)
        pending.append((fixed[:i]+((p,e,True,True),)+fixed[i+1:],ix,path+(label+(True,),)))
        pending.append((fixed[:i]+((p,e+2,True,False),)+fixed[i+1:],ix,path+(label+(False,),)))
    else:
        box = fixed + tuple((p,2,False,False) for p in primes[ix:ix+4-len(fixed)])
        assert box == from_source.pop(path), (path,box)
        low = prod(sum(F(1,p**i) for i in range(e+1)) if pp else 1 for p,e,pp,ee in box)
        high = prod(sum(F(1,p**i) for i in range(e+1)) if pp and ee else F(p,p-1) for p,e,pp,ee in box)
        lower_n = prod(p**e for p,e,pp,ee in box)
        assert (2<=low) if tag=="A" else (high+F(1,lower_n)<2)
        counts[tag]+=1
assert not pending and not from_source
print("All generated Lean branches, ordered tests, boxes and exact inequalities match:",dict(counts))

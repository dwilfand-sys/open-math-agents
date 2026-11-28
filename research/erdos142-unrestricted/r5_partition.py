"""Resumable native-cardinality SAT audit with explicit prefix cubes.
Auxiliary search; independent CP-SAT remains the second primary formulation.
"""
import argparse,itertools,json,time,pathlib
from pysat.solvers import Solver
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=117)
p.add_argument('--target',type=int,default=69);p.add_argument('--seconds',type=int,default=4500)
p.add_argument('--table',default='/tmp/r5-table.txt');p.add_argument('--out',default='work/r5-117-partition.json')
p.add_argument('--split-bits',type=int,default=6)
a=p.parse_args();t=time.monotonic();N=a.n
cap={0:0,116:68}
for line in open(a.table):
 if line.strip() and not line.startswith('#'):
  k,v=map(int,line.split());cap[k]=v
s=Solver(name='minicard');xs=list(range(1,N+1));s.add_atmost(xs,a.target);s.add_atmost([-x for x in xs],N-a.target)
windows=0
for d in range(1,(N-1)//4+1):
 for b in range(1,N-4*d+1):s.add_clause([-b-j*d for j in range(5)])
 for r in range(1,d+1):
  row=list(range(r,N+1,d));L=len(row)
  for m in range(6,min(116,L)+1):
   if cap[m]==cap[m-1]+1:continue
   if m<L and m+1 in cap and cap[m+1]==cap[m]:continue
   for lo in range(L-m+1):s.add_atmost(row[lo:lo+m],cap[m]);windows+=1
for k in range(1,min(N,116)+1):
 s.add_atmost(xs[:k],cap[k]);s.add_atmost(xs[-k:],cap[k])
# Explicit lower corridor; logically redundant with total+suffix bounds but
# essential for propagation. In particular this forces the four endpoints.
for j in range(1,N):
 if N-j in cap:
  lower=max(0,a.target-cap[N-j])
  s.add_atmost([-v for v in xs[:j]],j-lower)
  s.add_atmost([-v for v in xs[-j:]],j-lower)
# Lower bounds for every AP subwindow from a disjoint partition of its
# complement. Other residue classes and the two ends of this residue class
# each have the ordinary table upper bound. No external search result is used.
for length in range(117,N+1):cap[length]=cap[length-1]+1
complement_cuts=0
for d in range(1,(N-1)//4+1):
 rows=[list(range(r,N+1,d)) for r in range(1,d+1)]
 total_upper=sum(cap[len(row)] for row in rows)
 for row in rows:
  L=len(row);other_upper=total_upper-cap[L]
  for lo in range(L):
   for hi in range(lo+1,L+1):
    lower=a.target-other_upper-cap[lo]-cap[L-hi]
    if lower>0:
     s.add_atmost([-x for x in row[lo:hi]],hi-lo-lower);complement_cuts+=1
print(json.dumps({'event':'model','complement_cuts':complement_cuts,'seconds':time.monotonic()-t}),flush=True)
# No symmetry condition: every assignment has exactly one of these 64 prefixes.
assert 0<=a.split_bits<=6
split=list(range(3,3+a.split_bits)); cubes=list(itertools.product([0,1],repeat=len(split)))
pending=list(range(len(cubes)));closed=[];rounds=0;witness=None;last_report=t
def checkpoint():
 z={'n':N,'target':a.target,'status':'SAT' if witness else ('UNSAT' if not pending else 'UNKNOWN'),'split_positions':split,'closed_cubes':closed,'remaining_cubes':[{'index':i,'bits':list(cubes[i])} for i in pending],'witness':witness,'seconds':time.monotonic()-t,'stats':s.accum_stats(),'model':'native cardinality; no symmetry; OEIS through115 and r5(116)<=68'}
 pathlib.Path(a.out).write_text(json.dumps(z,indent=2)+'\n');return z
while pending and time.monotonic()-t<a.seconds and witness is None:
 for i in pending.copy():
  if time.monotonic()-t>=a.seconds:break
  ass=[x if b else -x for x,b in zip(split,cubes[i])]
  s.conf_budget(10000);v=s.solve_limited(assumptions=ass);rounds+=1
  if v is False:pending.remove(i);closed.append({'index':i,'bits':list(cubes[i])})
  elif v is True:
   model=set(s.get_model());witness=[x for x in xs if x in model]
   assert len(witness)==a.target
   W=set(witness);assert not any(all(b+j*d in W for j in range(5)) for d in range(1,(N-1)//4+1) for b in range(1,N-4*d+1))
  checkpoint()
  if v is not None or time.monotonic()-last_report>30:
   print(json.dumps({'cube':i,'verdict':v,'closed':len(closed),'remaining':len(pending),'seconds':time.monotonic()-t,**s.accum_stats()}),flush=True);last_report=time.monotonic()
  if witness is not None:break
print(json.dumps(checkpoint()),flush=True)

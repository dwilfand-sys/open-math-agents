"""Independent CP-SAT formulation: select holes hitting every 5-AP.

Uses integer interval/AP-window lower bounds on holes. Does not share code,
CNF, symmetry encoding, or precomputed domains with r5_sat.py.
"""
import argparse, json, time, pathlib
from ortools.sat.python import cp_model

p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=117)
p.add_argument('--target',type=int,default=69);p.add_argument('--seconds',type=int,default=5400)
p.add_argument('--out',default='work/r5-cp-result.json');p.add_argument('--table',default='/tmp/r5-table.txt')
a=p.parse_args();t=time.monotonic();N=a.n
table={0:0,116:68}
for line in open(a.table):
 if line.strip() and not line.startswith('#'):
  u,v=map(int,line.split());table[u]=v
m=cp_model.CpModel();h={i:m.new_bool_var('hole_%d'%i) for i in range(1,N+1)}
m.add(sum(h.values())==N-a.target)
for j in range(1,N):
 if N-j in table:
  required=max(0,a.target-table[N-j])
  m.add(sum(h[i] for i in range(1,j+1))<=j-required)
  m.add(sum(h[i] for i in range(N-j+1,N+1))<=j-required)
windows=0
for step in range(1,N):
 for first in range(1,N+1):
  length=(N-first)//step+1
  if length<5:break
  progression=[]
  for k in range(1,min(length,116)+1):
   progression.append(h[first+(k-1)*step])
   if k>=5:
    m.add(sum(progression)>=k-table[k]);windows+=1
# Independent, simple symmetry: total holes in the left half <= right half.
# Any solution can be reflected to satisfy this, and no paired-bit encoding is used.
m.add(sum(h[i] for i in range(1,N//2+1)) <= sum(h[i] for i in range(N-N//2+1,N+1)))
solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=a.seconds
solver.parameters.num_search_workers=2;solver.parameters.log_search_progress=True
solver.parameters.random_seed=357
print(json.dumps({'event':'built','n':N,'target':a.target,'windows':windows,'seconds':time.monotonic()-t}),flush=True)
verdict=solver.solve(m)
result={'method':'ortools-cp-sat-hitting-set','n':N,'target':a.target,'status':solver.status_name(verdict),'seconds':time.monotonic()-t,'branches':solver.num_branches,'conflicts':solver.num_conflicts,'summary':solver.response_stats(),'assumed_caps':'A003004 through115; r5(116)=68'}
if verdict in [cp_model.OPTIMAL,cp_model.FEASIBLE]:
 w=[i for i in h if not solver.value(h[i])];S=set(w)
 assert len(w)==a.target
 assert not any(all(b+j*d in S for j in range(5)) for b in S for d in range(1,(N-b)//4+1))
 result['witness']=w
pathlib.Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)

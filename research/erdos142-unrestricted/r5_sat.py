"""Exact unrestricted r_5(N) feasibility: SAT plus sound OEIS window caps.

The five-term clauses and exact cardinality alone define the problem.
Window caps are redundant inequalities from A003004 through 115 and r5(116)=68.
No previously computed residue or symmetry exclusion is assumed.
"""
import argparse, json, time, pathlib, hashlib
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

p=argparse.ArgumentParser()
p.add_argument('--n',type=int,default=117);p.add_argument('--target',type=int,default=69)
p.add_argument('--seconds',type=int,default=5400);p.add_argument('--table',default='/tmp/r5-table.txt')
p.add_argument('--out',default='work/r5-sat-result.json')
a=p.parse_args(); start=time.monotonic(); n=a.n; target=a.target
caps={0:0,**{int(k):int(v) for k,v in (s.split() for s in open(a.table) if s.strip() and not s.startswith('#'))}}
caps[116]=68
pool=IDPool(start_from=n+1); s=Solver(name='cadical195'); count=0
def add(cs):
 global count
 s.append_formula(cs);count+=len(cs)
def bound(xs,b):
 if b>=len(xs):return
 if b<0: add([[]]);return
 if b==len(xs)-1:add([[-x for x in xs]]);return
 add(CardEnc.atmost(xs,bound=b,vpool=pool,encoding=EncType.cardnetwrk).clauses)

add(CardEnc.equals(list(range(1,n+1)),bound=target,vpool=pool,encoding=EncType.cardnetwrk).clauses)
aps=[]
for d in range(1,(n-1)//4+1):
 for b in range(1,n-4*d+1):
  q=[b+i*d for i in range(5)];aps.append(q);add([[-v for v in q]])
# Prefix and suffix corridors are particularly useful. All selected constraints
# are valid on arbitrary AP windows; omitted redundant windows affect speed only.
windows=0
for d in range(1,(n-1)//4+1):
 for residue in range(1,d+1):
  row=list(range(residue,n+1,d));L=len(row)
  for m in range(6,min(L,116)+1):
   u=caps[m]
   if u==caps[m-1]+1:continue # implied by an (m-1)-window plus one bit
   for lo in range(L-m+1):
    # A same-cap extension implies this constraint when such an extension exists.
    if m<L and m+1 in caps and caps[m+1]==u:continue
    bound(row[lo:lo+m],u);windows+=1
for j in range(1,min(n,116)+1):
 bound(list(range(1,j+1)),caps[j]);bound(list(range(n-j+1,n+1)),caps[j])
# Reflection breaking: lexicographically prefer x >= reverse(x).
# e_i is EXACTLY the equality of the first i reflected pairs.
prev=pool.id();add([[prev]])
for i in range(1,n//2+1):
 x,y=i,n+1-i;e=pool.id()
 add([[-prev,x,-y],[-e,prev],[-e,-x,y],[-e,x,-y],[-prev,x,y,e],[-prev,-x,-y,e]])
 prev=e
print(json.dumps({'event':'built','n':n,'target':target,'variables':pool.top,'clauses':count,'windows':windows,'aps':len(aps),'seconds':time.monotonic()-start}),flush=True)
status=None;rounds=0
while time.monotonic()-start<a.seconds:
 s.conf_budget(20000);status=s.solve_limited();rounds+=1
 print(json.dumps({'event':'checkpoint','round':rounds,'seconds':time.monotonic()-start,'status':status,**s.accum_stats()}),flush=True)
 if status is not None:break
result={'method':'cadical195-cardinality-networks','n':n,'target':target,'status':('SAT' if status else 'UNSAT') if status is not None else 'UNKNOWN','seconds':time.monotonic()-start,'stats':s.accum_stats(),'clauses':count,'variables':pool.top,'assumed_caps':'A003004 through115; r5(116)=68','table_sha256':hashlib.sha256(pathlib.Path(a.table).read_bytes()).hexdigest()}
if status:
 model=set(s.get_model());w=[i for i in range(1,n+1) if i in model]
 assert len(w)==target and all(not all(x in model for x in q) for q in aps)
 result['witness']=w
pathlib.Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)

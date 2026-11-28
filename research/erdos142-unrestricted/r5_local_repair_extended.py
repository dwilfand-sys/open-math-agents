"""Local repair of Draconna's board #200424 near witness. No table caps."""
import json,time,pathlib
from pysat.solvers import Solver
from ortools.sat.python import cp_model
mask=632625408446542538220931436864347870
source=[i for i in range(1,119) if mask>>i&1]
assert len(source)==70
results=[]
for N,K,A in [(118,70,source),(117,69,[i for i in source if i<=117])]:
 aps=[list(range(b,b+5*d,d)) for d in range(1,(N-1)//4+1) for b in range(1,N-4*d+1)]
 bad=[w for w in aps if set(w)<=set(A)];assert bad==[[10,35,60,85,110]]
 for radius in [4,5]:
  # Since cardinality is preserved, radius deletions = radius insertions.
  for method in ['minicard','cp-sat']:
   t=time.monotonic();witness=None
   if method=='minicard':
    s=Solver(name='minicard');V=list(range(1,N+1))
    s.add_atmost(V,K);s.add_atmost([-v for v in V],N-K)
    for w in aps:s.add_clause([-v for v in w])
    s.add_atmost([-i for i in A],radius)
    s.conf_budget(300000);ans=s.solve_limited()
    status='SAT' if ans else 'UNSAT' if ans is False else 'UNKNOWN'
    if ans:witness=[i for i in V if i in set(s.get_model())]
    stats=s.accum_stats();s.delete()
   else:
    m=cp_model.CpModel();x=[m.new_bool_var(str(i)) for i in range(N+1)]
    m.add(sum(x[1:])==K)
    for w in aps:m.add(sum(x[i] for i in w)<=4)
    m.add(sum(x[i] for i in A)>=K-radius)
    s=cp_model.CpSolver();s.parameters.max_time_in_seconds=15;s.parameters.num_search_workers=1
    ans=s.solve(m);status=s.status_name(ans)
    if ans in [cp_model.FEASIBLE,cp_model.OPTIMAL]:witness=[i for i in range(1,N+1) if s.value(x[i])]
    stats={'branches':s.num_branches,'conflicts':s.num_conflicts}
   if witness:
    assert len(witness)==K and not any(set(w)<=set(witness) for w in aps)
   r={'n':N,'target':K,'radius':radius,'method':method,'status':status,'seconds':time.monotonic()-t,'stats':stats,'witness':witness}
   results.append(r);print(json.dumps(r),flush=True)
   pathlib.Path('work/r5-local-repair-extended-results.json').write_text(json.dumps({'source':'Draconna note #200424','source_mask':str(mask),'results':results},indent=2)+'\n')

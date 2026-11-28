"""Solver-free exhaustive repair replay; only integer bit operations.
Credit: source near witness Draconna #200424. Enumerates all removals and
all legal, increasing-order insertions. Reports complete tree counts.
"""
import itertools,json,time
M=632625408446542538220931436864347870
out=[]
for N in [118,117]:
 t=time.monotonic();A=M&((1<<(N+1))-1);selected=[i for i in range(1,N+1) if A>>i&1];missing=[i for i in range(1,N+1) if not A>>i&1]
 aps=[sum(1<<(b+j*d) for j in range(5)) for d in range(1,N//4+1) for b in range(1,N-4*d+1)]
 bad=[e for e in aps if A&e==e];assert len(bad)==1
 edges={i:[e^(1<<i) for e in aps if e>>i&1] for i in missing}
 totals=[]
 for r in [4]:
  removed_cases=0;rejected_before_insert=0;nodes=0;leaves=0;found=[]
  def visit(S,available,k):
   global nodes,leaves
   nodes+=1
   if k==0:leaves+=1;found.append(S);return
   legal=[v for v in available if all(S&e!=e for e in edges[v])]
   if len(legal)<k:return
   for j,v in enumerate(legal[:len(legal)-k+1]):visit(S|(1<<v),legal[j+1:],k-1)
  for D in itertools.combinations(selected,r):
   rm=sum(1<<v for v in D)
   if not(rm&bad[0]):rejected_before_insert+=1;continue
   removed_cases+=1;visit(A^rm,missing,r)
  assert not found
  row={'n':N,'radius':r,'removal_cases':removed_cases,'removals_rejected_by_original_AP':rejected_before_insert,'insertion_nodes':nodes,'feasible_leaves':leaves};totals.append(row);print(json.dumps(row),flush=True)
 out.append({'n':N,'source_mask':str(A),'seconds':time.monotonic()-t,'complete':True,'cases':totals})
open('work/r5-repair-replay-four-results.json','w').write(json.dumps(out,indent=2)+'\n')

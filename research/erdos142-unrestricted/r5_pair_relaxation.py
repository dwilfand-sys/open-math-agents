"""Level-two Boolean moment relaxation with separated AP-window cuts.
No UNSAT result is a certificate until its numerical dual is reconstructed exactly.
For an exact-K set, y_ij=x_i*x_j and sum_j y_ij=K*x_i.
Window sum<=c implies sum_i_in_W y_ij<=c*x_j and
sum_i_in_W(x_i-y_ij)<=c*(1-x_j). All are necessary conditions.
"""
import argparse,json,time,pathlib
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,csr_matrix,vstack
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=117);p.add_argument('--target',type=int,default=69);p.add_argument('--rounds',type=int,default=12);p.add_argument('--seconds',type=int,default=420);p.add_argument('--table',default='/tmp/r5-table.txt');p.add_argument('--out',default='work/r5-pair-relaxation.json');a=p.parse_args();N=a.n;K=a.target;start=time.monotonic()
cap={0:0,116:68}
for line in open(a.table):
 if line.strip() and not line.startswith('#'):
  k,v=map(int,line.split());cap[k]=v
idx=np.zeros((N,N),dtype=np.int32);cols=N
for i in range(N):
 idx[i,i]=i
 for j in range(i):idx[i,j]=idx[j,i]=cols;cols+=1
windows=[];caps=[]
for d in range(1,(N-1)//4+1):
 for b in range(N):
  L=(N-1-b)//d+1
  for k in range(5,min(116,L)+1):
   if cap[k]==cap[k-1]+1:continue
   windows.append(np.arange(b,b+k*d,d));caps.append(cap[k])
caps=np.array(caps)
rr=[];cc=[];vv=[];rhs=[]
def add(items,b):
 row=len(rhs);rhs.append(float(b))
 for c,v in items:rr.append(row);cc.append(int(c));vv.append(float(v))
for W,c in zip(windows,caps):add([(i,1) for i in W],c)
for i in range(N):
 for j in range(i):
  q=idx[i,j];add([(q,1),(i,-1)],0);add([(q,1),(j,-1)],0);add([(i,1),(j,1),(q,-1)],1)
A=coo_matrix((vv,(rr,cc)),shape=(len(rhs),cols)).tocsr();B=np.array(rhs)
er=[];ec=[];ev=[]
for i in range(N):
 er.append(0);ec.append(i);ev.append(1)
 for j in range(N):er.append(i+1);ec.append(int(idx[i,j]));ev.append(1)
 er.append(i+1);ec.append(i);ev.append(-K)
E=coo_matrix((ev,(er,ec)),shape=(N+1,cols)).tocsr();F=np.array([K]+[0]*N)
wr=[];wc=[]
for q,W in enumerate(windows):wr.extend([q]*len(W));wc.extend(W)
Wmat=coo_matrix((np.ones(len(wr)),(wr,wc)),shape=(len(windows),N)).tocsr()
seen=set();history=[];status='UNFINISHED'
for iteration in range(a.rounds):
 left=a.seconds-(time.monotonic()-start)
 if left<=0:break
 r=linprog(np.zeros(cols),A_ub=A,b_ub=B,A_eq=E,b_eq=F,bounds=(0,1),method='highs',options={'time_limit':left})
 row={'iteration':iteration,'status':int(r.status),'message':r.message,'seconds':time.monotonic()-start,'inequalities':A.shape[0]}
 if not r.success:
  status='NUMERICAL_INFEASIBLE' if r.status==2 else 'UNKNOWN';history.append(row);print(json.dumps(row),flush=True);break
 x=r.x[:N];Y=r.x[idx];sums=Wmat@Y;totals=Wmat@x
 violations=np.stack((sums-caps[:,None]*x[None,:],totals[:,None]-sums-caps[:,None]*(1-x[None,:])))
 row['max_violation']=float(violations.max());history.append(row);print(json.dumps(row),flush=True)
 if violations.max()<1e-7:status='RELAXATION_FEASIBLE';break
 candidates=np.argpartition(violations.ravel(),-min(2000,violations.size))[-min(2000,violations.size):]
 rr=[];cc=[];vv=[];rhs=[]
 for ix in candidates:
  typ,q,j=map(int,np.unravel_index(ix,violations.shape))
  if violations[typ,q,j]<=1e-7 or (typ,q,j) in seen:continue
  seen.add((typ,q,j));W=windows[q];c=int(caps[q])
  if typ==0:add([(idx[i,j],1) for i in W]+[(j,-c)],0)
  else:add([(i,1) for i in W]+[(idx[i,j],-1) for i in W]+[(j,c)],c)
 if not rhs:status='NUMERICAL_STALL';break
 new=coo_matrix((vv,(rr,cc)),shape=(len(rhs),cols)).tocsr();A=vstack([A,new],format='csr');B=np.concatenate([B,rhs])
 pathlib.Path(a.out).write_text(json.dumps({'n':N,'target':K,'status':'RUNNING','history':history},indent=2)+'\n')
result={'n':N,'target':K,'status':status,'seconds':time.monotonic()-start,'history':history,'warning':'floating-point relaxation only; no exact infeasibility certificate'}
pathlib.Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)

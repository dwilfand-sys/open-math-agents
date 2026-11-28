import argparse
p=argparse.ArgumentParser();p.add_argument("--table",default="b003004.txt");a=p.parse_args()
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix
cap={0:0,116:68}
for line in open(a.table):
 if line.strip() and not line.startswith('#'):
  k,v=map(int,line.split());cap[k]=v
for N,K in [(117,69),(118,70)]:
 rows=[]; bs=[]
 for d in range(1,(N-1)//4+1):
  for b in range(1,N+1):
   L=(N-b)//d+1
   for k in range(5,min(116,L)+1):
    if cap[k]==cap[k-1]+1:continue
    rows.append(list(range(b-1,b+(k-1)*d,d)));bs.append(cap[k])
 A=lil_matrix((len(rows),N))
 for i,row in enumerate(rows):A[i,row]=1
 r=linprog(-np.ones(N),A_ub=A.tocsr(),b_ub=bs,bounds=[(1,1) if i in ([0,1,115,116] if N==117 else [0,1,2,115,116,117]) else (0,1) for i in range(N)],method='highs')
 print(N,r.status,-r.fun if r.success else r.message,len(rows),flush=True)

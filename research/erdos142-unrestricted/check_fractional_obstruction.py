"""Exact rational feasibility of every AP-window cap, not a real set."""
from fractions import Fraction as F
import json,argparse
p=argparse.ArgumentParser();p.add_argument('--table',default='/tmp/r5-table.txt');p.add_argument('--out',default='work/r5-fractional-obstruction.json');a=p.parse_args()
cap={0:0,116:68}
for line in open(a.table):
 if line.strip() and not line.startswith('#'):
  k,v=map(int,line.split());cap[k]=v
results=[]
for N,K in [(117,69),(118,70)]:
 if N==117:x={i:F(1) if i in [1,2,116,117] else F(65,113) for i in range(1,N+1)}
 else:x={i:F(1) if i in [1,2,3,116,117,118] else F(1,2) if i in [4,5,114,115] else F(31,54) for i in range(1,N+1)}
 assert sum(x.values())==K
 checked=0;bad=[]
 for d in range(1,N):
  for first in range(1,N+1):
   total=F(0)
   for k in range(1,min(116,(N-first)//d+1)+1):
    total+=x[first+(k-1)*d];checked+=1
    if total>cap[k]:bad.append([first,d,k,str(total),cap[k]])
 result={'n':N,'target':K,'checks':checked,'bad':bad,'weights':{str(k):str(v) for k,v in x.items()}}
 results.append(result);print(json.dumps({k:v for k,v in result.items() if k!='weights'}))
open(a.out,'w').write(json.dumps(results,indent=2)+'\n')

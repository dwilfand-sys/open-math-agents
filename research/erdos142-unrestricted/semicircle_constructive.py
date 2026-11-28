"""Construct a unit multiplier putting a nonexceptional triple in a semicircle.
Independent of check_semicircle.cpp's exhaustive search over all units.
"""
import itertools,math,random,json

def large_gap(n,points):
 q=sorted(points)
 return max(q[1]-q[0],q[2]-q[1],n+q[0]-q[2])

def exceptional(n,points):
 p=sorted(points)
 anti=n%2==0 and any((a-b)%n==n//2 for a,b in itertools.combinations(p,2))
 equi=n%3==0 and large_gap(n,p)==n//3
 return anti or equi

def multiplier(n,points):
 p=sorted((x-min(points))%n for x in points)
 if exceptional(n,p):return None
 if 2*large_gap(n,p)>n:return 1
 if n%2 and n>=3:
  base=2
 elif n%4==0:
  if any(x%2 for x in p):
   u=1+n//2
   assert 2*large_gap(n,[(u*x)%n for x in p])>n
   return u
  u=multiplier(n//2,[x//2 for x in p]);assert u is not None
  assert math.gcd(u,n)==1
  return u
 else:
  if all(x%2==0 for x in p):
   u=multiplier(n//2,[x//2 for x in p]);assert u is not None
   return u if u%2 else u+n//2
  base=n//2+2
 u=1
 for _ in range(n.bit_length()+3):
  u=u*base%n
  if 2*large_gap(n,[(u*x)%n for x in p])>n:
   assert math.gcd(u,n)==1
   return u
 raise AssertionError(('iteration bound failed',n,p,base))

def verify(n,p):
 u=multiplier(n,p)
 if u is None:
  assert exceptional(n,p)
 else:
  assert math.gcd(u,n)==1
  assert 2*large_gap(n,[(u*x)%n for x in p])>n

if __name__=='__main__':
 count=0
 for n in range(3,151):
  for a,b in itertools.combinations(range(1,n),2):
   verify(n,[0,a,b]);count+=1
 rng=random.Random(142)
 for _ in range(100000):
  n=rng.randrange(3,10**12);p=rng.sample(range(n),3);verify(n,p)
 print(json.dumps({'exhaustive_normalized_triples':count,'all_moduli_through':150,'random_triples':100000,'random_modulus_upper_bound':10**12,'seed':142,'status':'passed'}))

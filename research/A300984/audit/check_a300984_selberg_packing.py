"""Independent exact tests of the finite Selberg argument."""
from fractions import Fraction as Q
from math import gcd, isqrt, lcm, prod
from lagneau_selberg_packing import coefficient_intervals,packed_mass,combined_mass


def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]


def factors(n):
    out=[]
    for p in range(2,isqrt(n)+1):
        while n%p==0:
            out.append(p)
            n//=p
    return out+([n] if n>1 else [])


def prime(n):
    return n>=2 and all(n%p for p in range(2,isqrt(n)+1))


def test(z):
    ds=[d for d in range(1,z+1) if gcd(d,6)==1 and len(factors(d))==len(set(factors(d)))]
    g={d:Q(2**len(factors(d)),d) for d in ds}
    h={d:prod((Q(2,p-2) for p in factors(d)),start=Q(1)) for d in ds}
    G=sum(h.values())
    K=sum(h[d]*prod(1+p for p in factors(d)) for d in ds)
    lam={d:(-1)**len(factors(d))*sum(h[a] for a in ds if a%d==0)/(G*g[d]) for d in ds}
    assert lam[1]==1
    exact=sum(lam[d]*lam[e]*Q(2**len(factors(lcm(d,e))),lcm(d,e)) for d in ds for e in ds)
    assert exact==1/G
    assert K/G==sum(2**len(factors(d))*abs(lam[d]) for d in ds)
    lo,up=coefficient_intervals([z])[z]
    assert lo<=G and up>=K
    for start in (10000,10001,17393):
        for width in (73,351,2049):
            found=[r for r in range(start,start+width+1) if prime(r) and prime(2*r-1)]
            assert len(found)<=(Q(width,6)+1)/G+(K/G)**2
            assert sum(Q(1,r) for r in found)>=packed_mass(start+width,len(found),(lo,up))
    # Choose a dense hypothetical collection packed maximally at the top and
    # large enough to exercise the nontrivial rank bound, independent of
    # whether finding all such putative primes would be feasible.
    count=1+int(4*(K/G)**2)
    top=10**8
    distances=[max(0,(6*G*(j-1/G-(K/G)**2)).__ceil__()) for j in range(1,count+1)]
    actual=sum(Q(1,top-d) for d in distances)
    assert Q(count,top)<packed_mass(top,count,(lo,up),16)<=actual
    assert Q(count,top)<combined_mass(top,count,{z:(lo,up)},16)<=actual


if __name__=='__main__':
    for z in (7,13,25,37):
        test(z)
    print('Four exact sieve forms, 36 concrete prime intervals, four nontrivial rank tests passed.')

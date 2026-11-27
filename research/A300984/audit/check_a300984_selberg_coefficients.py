"""Replay the production sieve coefficient intervals by prime-product enumeration."""
from bisect import bisect_left
from math import isqrt
from lagneau_selberg_packing import coefficient_intervals,SCALE


def recompute(levels):
    largest=max(levels)
    sieve=bytearray([1])*(largest+1)
    for p in range(2,isqrt(largest)+1):
        if sieve[p]:
            sieve[p*p::p]=bytes(1+(largest-p*p)//p)
    primes=[p for p in range(5,largest+1,2) if sieve[p]]
    gs=[0]*len(levels)
    ks=[0]*len(levels)
    def visit(d,i,numer,den,extra):
        # numer/den is the exact h(d). extra is the exact product of p+1.
        j=bisect_left(levels,d)
        gs[j]+=SCALE*numer//den
        ks[j]+=(SCALE*numer*extra+den-1)//den
        while i<len(primes):
            p=primes[i]
            if p*d>largest:
                break
            visit(p*d,i+1,2*numer,(p-2)*den,(p+1)*extra)
            i+=1
    visit(1,0,1,1,1)
    result={}
    g=k=0
    for i,z in enumerate(levels):
        g+=gs[i]
        k+=ks[i]
        result[z]=(g,k)
    return result


if __name__=='__main__':
    levels=[1000,3000,10000,20000,30000,50000,70000,100000,150000,
            200000,300000,500000,700000,1000000,1500000,2000000]
    direct=recompute(levels)
    for z,(gl,ku) in coefficient_intervals(levels).items():
        g,k=direct[z]
        assert gl*SCALE<=g and ku*SCALE>=k
        assert g-gl*SCALE<z and ku*SCALE-k<100*z
    print('All 16 exact prime-product replays confirmed the stored rounding directions.')

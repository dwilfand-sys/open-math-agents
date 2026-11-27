"""Check local residues and exact finite examples for the squarefree A400795 family."""

from fractions import Fraction
from math import gcd, isqrt, prod


def least_prime_table(n):
    least = list(range(n+1))
    for p in range(2, isqrt(n)+1):
        if least[p] == p:
            for j in range(p*p, n+1, p):
                if least[j] == j:
                    least[j] = p
    return least


def prime_factors(n, least):
    factors = []
    while n > 1:
        p = least[n]
        factors.append(p)
        n //= p
    return factors


def excluded(residue, prime):
    if (2*residue-1) % prime == 0:
        return True
    modulus = prime if prime % 4 == 3 else prime*prime
    return (4*residue+1) % modulus == 0


def local_checks():
    least = least_prime_table(99)
    primes = [p for p in range(5,100) if least[p] == p]
    for p in primes:
        count = sum(excluded(r,p) for r in range(p*p) if r % p)
        exact = Fraction(2, p-1) if p % 4 == 3 else Fraction(p+1, p*(p-1))
        assert Fraction(count, p*(p-1)) == exact
        minus_root = (-pow(4,-1,p)) % p
        assert minus_root != pow(2,-1,p) and minus_root != 0
        # The extra square exclusion is the unique lift of the minus root.
        assert sum((4*(minus_root+k*p)+1) % (p*p)==0 for k in range(p)) == 1
    # Check CRT intersection probabilities, including the fixed p=1 (mod 3).
    for shape in ((5,7),(5,13),(7,11),(5,7,13)):
        modulus = 3*prod(p if p % 4 == 3 else p*p for p in shape)
        unit_count = prod((p-1) if p%4==3 else p*(p-1) for p in shape)
        favorable = sum(all(excluded(r,p) for p in shape)
                        for r in range(1,modulus,3) if gcd(r,modulus)==1)
        expected = prod(Fraction(2,p-1) if p%4==3 else Fraction(p+1,p*(p-1))
                        for p in shape)
        assert Fraction(favorable,unit_count) == expected
    print(f"Local exclusions for {len(primes)} primes and four mixed-modulus CRT "
          "intersections agree exactly.")


def census(lower=75000, upper=150000, rough=19):
    least = least_prime_table(4*upper+1)
    limit = 2*upper-1
    attained = bytearray(limit+1)
    for a in range(2,isqrt(2*limit)+1):
        for b in range(a,(2*limit)//(a+1)+1):
            n = (a*b+a+b-gcd(a,b))//2
            if n <= limit:
                attained[n] = 1
    candidates, missing = 0, []
    for p in range(lower+1,upper+1):
        if p%3 != 1 or least[p]!=p:
            continue
        n,N = 2*p-1,4*p+1
        nf,Nf = prime_factors(n,least),prime_factors(N,least)
        if min(nf)<=rough or any(q%4 != 1 for q in Nf):
            continue
        if len(set(nf))!=len(nf) or len(set(Nf))!=len(Nf):
            continue
        assert gcd(n,N)==1 and len(set(nf+Nf))==len(nf)+len(Nf)
        candidates += 1
        if not attained[n]:
            missing.append((p,n,N,nf,Nf))
    print(f"{candidates} candidates in the finite interval, of which {len(missing)} "
          "are strongly nontriangular by exhaustive enumeration.")
    for row in missing[:5]:
        print(row)
    return missing


if __name__=='__main__':
    local_checks()
    census()

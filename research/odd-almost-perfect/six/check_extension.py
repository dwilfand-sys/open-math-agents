from math import gcd, isqrt
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256

primes=[q for q in range(3,100,2) if all(q%j for j in range(2,isqrt(q)+1))]
hits=0
for p in primes:
    for exponent in range(2,14,2):
        g=(p**exponent-1)//(p-1)
        sigma=p*g+1
        for coef in range(1,64,2):
            b=(coef*sigma+p)//2
            d=coef*g+1
            s=2*b-d
            assert 1+s*sigma==2*b*p**exponent
            assert d>=2 and d*p<2*b<d*(p+1)
            assert (2*b)//d==p and (2*b-d*p)*g==d-1
            assert 2*b==coef*sigma+p
            hits+=1
print("Nonvacuous integer instances of every extension formula:",hits)
print("Lean SHA-256:",sha256((Path(__file__).parent/"PrimePowerExtension.lean").read_bytes()).hexdigest())

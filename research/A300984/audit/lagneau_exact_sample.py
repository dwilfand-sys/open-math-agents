"""Build an independently checkable, one-sided sample for A300984.

A structurally eligible prime belongs to the primitive class only when no
smaller shifted prime divides its shift. Certifying more represented
nonprimitive primes than all primitive primes is enough for the sample.
This does not enumerate the entire interval or prove the population's ratio.
"""

from argparse import ArgumentParser
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
from math import gcd, isqrt, prod
from pathlib import Path
from random import Random
from shutil import which
from subprocess import run, TimeoutExpired
from time import monotonic

from sympy import factorint, isprime
from lagneau_prime_sample import primitive, SQUARES

FACTOR = which('factor') or r'C:\Program Files\Git\usr\bin\factor.exe'


def factor_values(values, seconds):
    try:
        out = run([FACTOR, *map(str, values)], capture_output=True, timeout=seconds,
                  text=True, check=True).stdout
    except TimeoutExpired:
        if len(values) > 1:
            middle = len(values)//2
            return (factor_values(values[:middle], seconds)
                    | factor_values(values[middle:], seconds))
        return {}
    results = {}
    for line in out.splitlines():
        lhs, rhs = line.split(':')
        n, fs = int(lhs), tuple(map(int, rhs.split()))
        if prod(fs) != n:
            raise ValueError('invalid factorization')
        results[n] = fs
    return results


def certified(q, known, certificates):
    if q < 2**64:
        # SymPy uses deterministic Miller-Rabin throughout this interval.
        return isprime(q)
    if q in known:
        return known[q]
    fs = factor_values([q-1], 0.8).get(q-1, ())
    if not fs or not all(certified(f, known, certificates) for f in set(fs)):
        known[q] = False
        return False
    bases = {}
    for f in sorted(set(fs)):
        for a in range(2, 100):
            if pow(a, q-1, q) == 1 and gcd(pow(a, (q-1)//f, q)-1, q) == 1:
                bases[f] = a
                break
        else:
            known[q] = False
            return False
    known[q] = True
    certificates[str(q)] = [fs, bases]
    return True


def main():
    parser=ArgumentParser()
    parser.add_argument('m',type=int)
    parser.add_argument('size',type=int)
    parser.add_argument('seed',type=int)
    parser.add_argument('--output',type=Path)
    a=parser.parse_args()
    assert 2 <= a.m <= 38
    limit = 10**a.m
    bound = isqrt(limit//4)
    rng = Random(a.seed)
    sample, negatives, primitive_count = [], {}, 0
    t0 = monotonic()
    while len(sample) < a.size:
        p = 12*rng.randint(1,(bound-1)//12)+1
        if not isprime(p):
            continue
        factors = factorint((p+1)//2)
        if any(e!=1 for e in factors.values()):
            continue
        assert prod(factors) == (p+1)//2 and all(isprime(q) for q in factors)
        pr = primitive(factors)
        sample.append([p, sorted(factors), pr])
        if pr:
            primitive_count += 1
            continue
        n, t = 4*p*p, 7
        while n <= limit:
            f = t*(p*p+p+1)-3*(p+1)
            if all(f%s for s in SQUARES):
                negatives[p] = (n, f)
                break
            n, t = n*2, t*2+1
    print('eligible', len(sample), 'primitive', primitive_count, 'nonprimitive candidate witnesses',
          len(negatives),'sampling seconds',round(monotonic()-t0,1),flush=True)
    available = list({v[1] for v in negatives.values()})
    batches = [available[i:i+8] for i in range(0,len(available),8)]
    known, certificates, valid = {}, {}, {}
    with ThreadPoolExecutor(2) as pool:
        for j, matches in enumerate(pool.map(lambda v: factor_values(v,2), batches)):
            for n, fs in matches.items():
                if len(fs) == len(set(fs)) and all(certified(f,known,certificates) for f in fs):
                    valid[n] = fs
            if j % 30 == 0:
                print('factor batches',j+1,'of',len(batches),'certified factorsets',len(valid),
                      'seconds',round(monotonic()-t0,1),flush=True)
    witnesses = {p:[n,f,valid[f]] for p,(n,f) in negatives.items() if f in valid}
    nlower = sum(1 for p,_,_ in sample if p in witnesses)
    artifact = {'m':a.m, 'sample_size':a.size, 'seed':a.seed,
                'sample':sample,'witnesses':witnesses,'primality_certificates':certificates}
    path = a.output or Path('lagneau_m'+str(a.m)+'_sample_'+str(a.seed)+'.json')
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(artifact, separators=(',',':')),encoding='utf8')
    print('certified represented nonprimitive', nlower,'all primitive',primitive_count,
          'unknown/unrepresented nonprimitive',len(sample)-primitive_count-nlower,'path',path,
          'seconds',round(monotonic()-t0,1),flush=True)


if __name__=='__main__':
    main()

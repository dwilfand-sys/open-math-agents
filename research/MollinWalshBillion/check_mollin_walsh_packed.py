"""Packed independent search for a two-square pair and an odd powerful offset."""
from math import isqrt
import sys
import numpy as np


def square_pair_bits(bound, residue):
    """Bit k marks a representation of 8k+residue."""
    count = (bound+1)//8
    bound = min(bound,8*(count-1)+residue)
    flags = np.zeros(count, dtype=np.bool_)
    roots = np.arange(isqrt(bound)+1, dtype=np.int64)
    sq = roots*roots
    for x in range(isqrt(bound//2)+1):
        sx = int(sq[x])
        stop = isqrt(bound-sx)+1
        for yr in range(4):
            if (sx+yr*yr)%8 != residue:
                continue
            start = x + (yr-x)%4
            if start < stop:
                flags[(sq[start:stop:4]+sx)//8] = True
    return int.from_bytes(np.packbits(flags,bitorder="little").tobytes(),"little")


def powerful_from_definition(n):
    # Check p^2 | n at every prime dividing n, by trial division.
    if n == 0:
        return True
    d = 2
    while d*d <= n:
        if n%d == 0:
            n //= d
            if n%d:
                return False
            while n%d == 0:
                n //= d
        d += 1
    return n == 1


def run(bound):
    if bound < 5655:
        raise ValueError("Use a bound of at least 5655")
    count = (bound+1)//8
    missing = (1<<count)-1
    pair = {r:square_pair_bits(bound,r) for r in (0,2,4)}
    print("bound",bound,"tested",count,"pair counts",[(r,v.bit_count()) for r,v in pair.items()],flush=True)
    used = []
    for c in range(3,min(200000,bound)+1,2):
        r = 7-c%8
        if r not in pair or not powerful_from_definition(c):
            continue
        shift = c//8
        if shift >= missing.bit_length():
            break
        # Truncate to the largest unresolved candidate before shifting.
        bits = pair[r]
        if missing.bit_length() < 1000000:
            bits &= (1<<(missing.bit_length()-shift))-1
        rest = missing & ~(bits<<shift)
        if rest != missing:
            used.append(c)
            missing = rest
    residual = []
    while missing:
        bit = missing & -missing
        residual.append(8*(bit.bit_length()-1)+7)
        missing ^= bit
    print("offsets",used,"residual",residual,flush=True)
    expected = [7,15,23,39,55,71,87,103,111,119,167,335,559,783,895,951,1455,1551,2127,5655]
    assert residual == expected
    # For each residual, exhaust every possible powerful third term and
    # confirm that a single factor of 4 is enough for representability.
    atoms = [x for x in range(4*max(residual)+1) if powerful_from_definition(x)]
    def restricted_witness(n):
        for c in atoms:
            if c>n:
                break
            for x in range(isqrt(n-c)+1):
                y=isqrt(n-c-x*x)
                if x*x+y*y==n-c:
                    return c,x,y
        return None
    for e in residual:
        assert restricted_witness(e) is None
        lift=restricted_witness(4*e)
        assert lift is not None
        print("two-square lift",e,*lift)
    pairs = {a+b:(a,b) for a in atoms for b in atoms if a<=b}
    exceptions = []
    for n in residual:
        for a in atoms:
            if n-a in pairs:
                print("witness", n, a, *pairs[n-a])
                break
        else:
            exceptions.append(n)
    for e in exceptions:
        a,b,c = next((a,*pairs[4*e-a]) for a in atoms if 4*e-a in pairs)
        print("four-times witness",4*e,a,b,c)
    assert exceptions == [v for v in (7,15,23,87,111,119) if v<=bound]
    print("exceptions",exceptions,flush=True)


if __name__ == "__main__":
    run(int(sys.argv[1]))

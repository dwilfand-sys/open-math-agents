"""Independent finite Mollin–Walsh check via Fermat's two-squares theorem."""
import sys
from math import isqrt
import numpy as np


def good_odd_units(max_k):
    """Index k is true precisely when 4k+1 is a sum of two squares."""
    limit = 4*max_k+1
    cap = isqrt(limit)
    prime = bytearray([1])*(cap+1)
    prime[:2]=b'\0\0'
    for d in range(2,isqrt(cap)+1):
        if prime[d]:
            prime[d*d::d]=bytes((cap-d*d)//d+1)
    defects = np.zeros(max_k+1,dtype=np.uint8)
    for p in range(3,cap+1,4):
        if not prime[p]:
            continue
        # Mark exactly the multiples having an odd p-adic valuation.
        d=p
        while d<=limit:
            first = (-pow(4,-1,d))%d
            defects[first::d]+=1
            step=d*p
            if step<=limit:
                second=(-pow(4,-1,step))%step
                defects[second::step]-=1
            d=step*p
    # An odd-valuation prime 3 mod 4 exceeding sqrt(limit) forces a
    # different such prime of smaller size, because 4k+1 is 1 mod 4.
    return defects==0


def pack(flags):
    return int.from_bytes(np.packbits(flags,bitorder="little").tobytes(),"little")


def masks(bound):
    n=(bound+1)//8
    unit=good_odd_units(n-1)
    # 8k+2 = 2(4k+1).
    out={2:pack(unit)}
    # 8k+4 = 4(2k+1); odd parts 3 mod 4 fail.
    arr=np.zeros(n,dtype=np.bool_)
    arr[::2]=unit[:(n+1)//2]
    out[4]=pack(arr)
    # 8k is representable precisely when k is. Each positive k with
    # odd part 1 mod 4 occurs as 2^a(4j+1) for a unique pair a,j.
    arr[:]=False
    arr[0]=True
    power=1
    while power<n:
        section=arr[power::4*power]
        section[:]=unit[:len(section)]
        power*=2
    out[0]=pack(arr)
    return out


def atoms(cap):
    # Each nonzero prime exponent >= 2 is of the form 2a+3b.
    return sorted({0}|{(a*a)*(b**3) for b in range(1,isqrt(cap)+1) if b**3<=cap
                        for a in range(1,isqrt(cap//b**3)+1)})


def run(bound):
    if bound<5655:
        raise ValueError("Use a bound of at least 5655")
    count=(bound+1)//8
    pair=masks(bound)
    print("candidate count",count,"pairs",[(r,b.bit_count()) for r,b in sorted(pair.items())],flush=True)
    unresolved=(1<<count)-1
    for c in atoms(min(200000,bound)):
        r=7-c%8
        if r in pair:
            unresolved &= ~(pair[r]<<(c//8))
            if unresolved.bit_length()<=c//8:
                break
    residual=[]
    while unresolved:
        ix=unresolved.bit_length()-1
        residual.append(8*ix+7)
        unresolved ^= 1<<ix
    residual.reverse()
    print("residual",residual,flush=True)
    expected=[7,15,23,39,55,71,87,103,111,119,167,335,559,783,895,951,1455,1551,2127,5655]
    assert residual==expected
    small=atoms(max(residual))
    pairs={x+y for x in small for y in small}
    exc=[n for n in residual if not any(n-z in pairs for z in small)]
    cap4=4*max(residual)
    large_atoms=atoms(cap4)
    two={x*x+y*y for x in range(isqrt(cap4)+1) for y in range(isqrt(cap4-x*x)+1)}
    for n in residual:
        assert not any(n-z in two for z in small)
        assert any(4*n-z in two for z in large_atoms)
    for e in exc:
        assert any(4*e-z in pairs for z in small)
    print("exceptions",exc,flush=True)
    assert exc==[n for n in (7,15,23,87,111,119) if n<=bound]


if __name__=="__main__":
    run(int(sys.argv[1]))

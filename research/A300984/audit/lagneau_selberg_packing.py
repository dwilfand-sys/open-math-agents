"""Unconditional capacity bound for a finite bin of second-kind Cunningham pairs."""
from array import array
from fractions import Fraction
from math import isqrt
from pathlib import Path
from check_a300984_published_singletons import COUNTS, reciprocal_lower

SCALE=10**20


def coefficient_intervals(limits):
    """Integer lower G(z), upper K(z), on one fixed denominator."""
    limits=sorted(set(limits))
    largest=max(limits)
    factor=array('I',[0])*(largest+1)
    for p in range(2,isqrt(largest)+1):
        if factor[p]:
            continue
        for j in range(p*p,largest+1,p):
            if not factor[j]:
                factor[j]=p
    h={1:SCALE}
    k={1:SCALE}
    gtotal=ktotal=SCALE
    result={}
    limit_set=set(limits)
    for d in range(2,largest+1):
        if d%2 and d%3:
            p=factor[d] or d
            m=d//p
            if m in h and m%p:
                h_value=h[m]*2//(p-2)
                k_value=(k[m]*(2*p+2)+p-3)//(p-2)
                # Any future squarefree multiple coprime to 6 is at least 5d.
                if 5*d<=largest:
                    h[d]=h_value
                    k[d]=k_value
                gtotal+=h_value
                ktotal+=k_value
        if d in limit_set:
            result[d]=(Fraction(gtotal,SCALE),Fraction(ktotal,SCALE))
    return result


def packed_mass(upper,count,stats,rank_bins=128):
    if not count:
        return Fraction()
    g,k=stats
    beta=1/g+(k/g)**2
    first=int(beta)+1
    mass=Fraction(count,upper)
    if first>count:
        return mass
    packed=Fraction(first-1,upper)
    width=(count-first+rank_bins)//rank_bins
    for lo in range(first,count+1,width):
        hi=min(lo+width-1,count)
        n=hi-lo+1
        # d_j >=6 G(j-beta), j counting primes in descending order.
        dsum=3*g*n*(lo+hi-2*beta)
        assert 0<=dsum<n*upper
        local=Fraction(n*n,n*upper-dsum)
        packed+=(local*SCALE).__floor__()/Fraction(SCALE)
    return max(mass,packed)


def combined_mass(upper,count,stats,rank_bins=128):
    """Use the strongest available level separately in each rank group."""
    if not count:
        return Fraction()
    capacity=[(g,1/g+(k/g)**2) for g,k in stats.values()]
    width=(count+rank_bins-1)//rank_bins
    mass=0
    for lo in range(1,count+1,width):
        hi=min(lo+width-1,count)
        n=hi-lo+1
        dsum=Fraction()
        for g,beta in capacity:
            start=max(lo,int(beta)+1)
            if start<=hi:
                dsum=max(dsum,3*g*(hi-start+1)*(start+hi-2*beta))
        assert 0<=dsum<n*upper
        part=Fraction(n*n,n*upper-dsum)
        mass+=(part*SCALE).__floor__()
    return max(Fraction(count,upper),Fraction(mass,SCALE))


def improve(windows,limits):
    bypower={}
    for path in windows:
        for line in path.read_text().splitlines():
            lo,hi,n=map(int,line.split())
            bypower.setdefault(len(str(lo)),[]).append((lo,hi,n))
    stats=coefficient_intervals(limits)
    oldtotal=newtotal=Fraction()
    for power,(before,after) in enumerate(zip(COUNTS,COUNTS[1:]),11):
        end=10**(power-1)
        unused=after-before
        fine=Fraction()
        for lo,hi,n in sorted(bypower.get(power,[])):
            assert lo==end and hi<=10**power and n>=0
            end=hi
            unused-=n
            fine+=reciprocal_lower(hi,n)
        assert unused>=0 and (end<10**power or unused==0)
        old=max(reciprocal_lower(10**power,after-before),fine+reciprocal_lower(10**power,unused))
        best=old
        choices=[]
        for z,pair in stats.items():
            part=fine+packed_mass(10**power,unused,pair)
            allbin=packed_mass(10**power,after-before,pair)
            answer=max(part,allbin)
            choices.append((answer,z))
            best=max(best,answer)
        best=max(best,fine+combined_mass(10**power,unused,stats),
                 combined_mass(10**power,after-before,stats))
        z=max(choices)[1]
        print(power,unused,z,round(float(best-old),10),round(float(best),10))
        oldtotal+=old
        newtotal+=best
    return oldtotal,newtotal


if __name__=='__main__':
    import sys
    from math import factorial
    previous=int(sys.argv[1])
    limits=list(map(int,sys.argv[2].split(',')))
    old,new=improve(list(map(Path,sys.argv[3:])),limits)
    ratio=Fraction(previous,10**15)/sum(new**k/factorial(k) for k in range(6))
    print('reciprocal lower, old then new:',float(old),float(new))
    print('exact rounded result:',(ratio*10**12).__ceil__(),'/ 10^12')

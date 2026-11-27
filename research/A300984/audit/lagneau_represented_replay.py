"""Independent six-position recurrence for the limiting represented fraction."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from math import gcd,isqrt
from lagneau_three_pattern_replay import primes_up_to


def symbol(a,n):
    # Jacobi symbol for a nonzero quadratic discriminant at an odd prime.
    a%=n
    sign=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5):sign=-sign
        if a%4==3 and n%4==3:sign=-sign
        a,n=n%a,a
    return sign if n==1 else 0


def roots(r,coefficients):
    exceptional=any((a*(a-3))%r==0 for a in coefficients)
    if r<32 or exceptional:
        sets=[set() for a in coefficients]
        for x in range(1,r*r-1):
            if x%r:
                for i,a in enumerate(coefficients):
                    if (a*x*x+(a-3)*(x+1))%(r*r)==0:
                        sets[i].add(x)
        assert len(set().union(*sets))==sum(map(len,sets))
        return list(map(len,sets))
    return [1+symbol(-3*(a-3)*(a+1),r) for a in coefficients]


def run(cutoff,K):
    prec=10**25
    masks=range(1<<K)
    states=[[j for j in range(K) if s & (1<<j)] for s in masks]
    neighbors=[[s^(1<<j) for j in idx] for s,idx in zip(masks,states)]
    lo=[prec]+[0]*((1<<K)-1)
    hi=lo.copy()
    coefficients=[2**(i+1)-1 for i in range(2,K+2)]
    for r in primes_up_to(cutoff):
        c=roots(r,coefficients)
        den=r*(r-1)-1
        stay=[den-sum(c)]
        for value in c:
            stay+= [x+value for x in stay]
        nlo,nhi=[],[]
        for s in masks:
            u,v=lo[s]*stay[s],hi[s]*stay[s]
            for j,k in zip(states[s],neighbors[s]):
                u+=c[j]*lo[k]
                v+=c[j]*hi[k]
            nlo.append(u//den)
            nhi.append(-(-v//den))
        lo,hi=nlo,nhi
    W=2310
    tail=Q(2*sum(gcd(j,W)==1 for j in range(W)),W*(cutoff//W*W-W-2))
    losses=[]
    for k in range(1,K+1):
        mask=(1<<k)-1
        lower=Q(sum(lo[s] for s in masks if s&mask==mask),prec)
        upper=sum(Q(hi[s],prec)*tail**((mask&~s).bit_count()) for s in masks)
        losses.append((lower,upper))
    # Write loss = f1 - sum_k w_(k+1)*(f_k-f_(k+1)),
    # where w_h=2^(-(h-1)/2) and f_(K+1) lies between 0 and f_K.
    digits=10**27
    lower,upper=losses[0]
    for k,(current,_hi) in enumerate(losses,1):
        next_lo,next_hi=losses[k] if k<K else (Q(0),_hi)
        root=isqrt(digits**2//(2**k))
        lower-=Q(root+1,digits)*(_hi-next_lo)
        upper-=Q(root,digits)*max(Q(0),current-next_hi)
    scale=10**15
    lowratio,highratio=(1-upper)*scale,(1-lower)*scale
    print(lowratio.numerator//lowratio.denominator,-(-highratio.numerator//highratio.denominator))
    # Recombination of the same binary-shell widths avoids interval cancellation.
    lo=Q(0)
    hi=Q(0)
    for k,(f_lo,f_hi) in enumerate(losses):
        a=isqrt(digits**2//2**k)
        b=isqrt(digits**2//2**(k+1))
        lo+=Q(a-b-1,digits)*f_lo
        hi+=Q(a-b+1,digits)*f_hi
    hi+=Q(b+1,digits)*f_hi
    lowratio,highratio=(1-hi)*scale,(1-lo)*scale
    print('direct shell sum',lowratio.numerator//lowratio.denominator,-(-highratio.numerator//highratio.denominator))


if __name__=='__main__':
    parser=ArgumentParser()
    parser.add_argument('cutoff',type=int)
    parser.add_argument('witnesses',type=int)
    args=parser.parse_args()
    if not 1<=args.witnesses<=6 or args.cutoff<100000 or args.cutoff%2:
        raise ValueError('Choose at most six tests and an even cutoff of at least 100,000')
    run(args.cutoff,args.witnesses)

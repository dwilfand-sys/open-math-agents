using System;
using System.Collections.Generic;

// Independent arithmetic check of the represented-prime frequencies in OEIS A300984.
// The direct factorization condition forces n=2^i p^j with i,j >= 2 and p=1 (mod 12).
public static class LagneauMajority
{
    static uint[] oddComposite;
    static List<int> trial;

    static long Sqrt(long n)
    {
        long r = (long)Math.Sqrt(n);
        while ((r+1) <= n/(r+1)) r++;
        while (r > 0 && r > n/r) r--;
        return r;
    }

    static void Sieve(int limit)
    {
        oddComposite = new uint[limit/64+1];
        for (int p=3; (long)p*p<=limit; p+=2)
            if (Prime(p))
                for (int k=p*p; k<=limit; k+=2*p)
                    oddComposite[k>>6] |= 1u << ((k>>1)&31);
        trial=new List<int> {2};
        for (int p=3; p<=Math.Min(limit,1500000); p+=2)
            if (Prime(p)) trial.Add(p);
    }

    static bool Prime(int p)
    {
        if (p==2) return true;
        return p>1 && (p&1)==1 && (oddComposite[p>>6] & (1u<<((p>>1)&31))) == 0;
    }

    // After all smaller prime factors are removed singly, a residual below
    // the current prime cubed has at most two prime factors with multiplicity.
    static bool Squarefree(long n)
    {
        if (n==0) return false;
        foreach (int p in trial)
        {
            if ((long)p*p*p > n) break;
            if (n%p != 0) continue;
            n/=p;
            if (n%p==0) return false;
        }
        long r=Sqrt(n);
        return n==1 || r*r!=n;
    }

    static bool Primitive(int p)
    {
        // Eligibility gives p = 1 (mod 12) and squarefree (p+1)/2.
        // Every smaller odd obstruction therefore has the form 2*d-1
        // for a proper divisor d of (p+1)/2. The prime 2 cannot obstruct.
        int half=(p+1)/2, rest=half;
        var divisors=new List<int>{1};
        foreach(int f in trial)
        {
            if ((long)f*f>rest) break;
            if (rest%f!=0) continue;
            rest/=f;
            int size=divisors.Count;
            for(int i=0;i<size;i++)
            {
                int d=divisors[i]*f;
                if(d<half && Prime(2*d-1)) return false;
                divisors.Add(d);
            }
        }
        if(rest>1)
        {
            for(int i=0;i<divisors.Count;i++)
            {
                int d=divisors[i]*rest;
                if(d<half && Prime(2*d-1)) return false;
            }
        }
        return true;
    }

    static long First(int p, long limit)
    {
        long s=3L*(1+p);
        if (!Squarefree(s)) return 0;
        long best=limit+1;
        long pe=(long)p*p;
        long ps=1+p+pe;
        while (pe<=(best-1)/4)
        {
            long n=4*pe, ts=7;
            while (n<best)
            {
                if (Squarefree(ts*ps-s)) {best=n;break;}
                if (n>(best-1)/2) break;
                n*=2;
                ts=ts*2+1;
            }
            if (pe>(best-1)/(4L*p)) break;
            pe*=p;
            ps+=pe;
        }
        return best<=limit ? best : 0;
    }

    public static void Run(int exponent)
    {
        if (exponent<7 || exponent>18) throw new ArgumentOutOfRangeException("exponent");
        long[] powers=new long[exponent+1];
        powers[0]=1;
        for (int i=1;i<=exponent;i++) powers[i]=10*powers[i-1];
        long limit=powers[exponent];
        int max=(int)Sqrt(limit/4);
        Sieve(max+1);
        int[] all=new int[exponent+1], yes=new int[exponent+1];
        for(int p=13; p<=max; p+=12)
        {
            if (!Prime(p)) continue;
            long n=First(p,limit);
            if (n==0) continue;
            bool good=Primitive(p);
            for (int e=7;e<=exponent;e++)
            {
                if(n>powers[e])continue;
                all[e]++;
                if(good)yes[e]++;
            }
        }
        for(int e=7;e<=exponent;e++)
            Console.WriteLine("{0} {1} {2} {3:F4}%",e,all[e],yes[e],100.0*yes[e]/all[e]);
    }
}

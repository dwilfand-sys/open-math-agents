using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Numerics;

// Sieve all the prime-divisor congruences T(n)=1 modulo rad(n).
// A surviving squarefree composite is certified by CRT. For other survivors
// we record n for a separate prime-power test. Prime squares are excluded.
public static class A279821Sieve
{
    static int[] Row(int p)
    {
        var a = new int[p];
        var inv = new int[p];
        a[0] = 1;
        a[1] = 1;
        inv[1] = 1;
        for (int i = 2; i < p; ++i) {
            inv[i] = (int)((long)(p-p/i)*inv[p%i]%p);
            a[i] = (int)((((2L*i-1)*a[i-1]+3L*(i-1)*a[i-2])%p)*inv[i]%p);
        }
        return a;
    }

    static bool One(int n, int p, int[] table)
    {
        if (p == 2) return true;
        long product = 1;
        while (n != 0 && product != 0) {
            product = product*table[n%p]%p;
            n /= p;
        }
        return product == 1;
    }

    public static int Main(string[] args)
    {
        int start = int.Parse(args[0], CultureInfo.InvariantCulture);
        int end = int.Parse(args[1], CultureInfo.InvariantCulture);
        int root = (int)Math.Sqrt(end);
        while ((long)(root+1)*(root+1)<=end) ++root;
        while ((long)root*root>end) --root;
        if (start < 2 || end < start || end == Int32.MaxValue) return 2;
        var ps = new List<int>();
        var small = new bool[root+1];
        var digits = new Dictionary<int,int[]>();
        for (int p=2; p<=root; ++p) {
            if (small[p]) continue;
            ps.Add(p);
            digits.Add(p, Row(p));
            for (int i=p*p; p<=root/p && i<=root; i+=p) small[i]=true;
        }
        var central = new BigInteger[root+1];
        central[0]=central[1]=1;
        for (int i=2;i<=root;++i)
            central[i]=((2*i-1)*central[i-1]+3*(i-1)*central[i-2])/i;
        long accepted=0, remaining=0;
        using (var log = new StreamWriter(args[2])) {
            for (int lo=start; lo<=end;) {
                int hi=(int)Math.Min((long)end, (long)lo+499999);
                int length=hi-lo+1;
                var rem=new int[length];
                var count=new byte[length];
                var repeated=new bool[length];
                for (int i=0;i<length;++i) rem[i]=lo+i;
                foreach (int p in ps) {
                    int initial=(p-lo%p)%p;
                    var row=digits[p];
                    for (int i=initial;i<length;i+=p) {
                        if (rem[i]==0) continue;
                        if (!One(lo+i,p,row)) {rem[i]=0; continue;}
                        ++count[i];
                        rem[i]/=p;
                        while(rem[i]%p==0) {rem[i]/=p; repeated[i]=true;}
                    }
                }
                for(int i=0;i<length;++i) {
                    if(rem[i]==0) continue;
                    int n=lo+i, q=rem[i];
                    if(q>1) {
                        if(count[i]==0) continue; // prime
                        ++count[i];
                        int d=n/q;
                        // Every surviving q > floor(sqrt(end)), hence d<q.
                        if(central[d]%q != BigInteger.One) continue;
                    }
                    if(count[i]==1) {
                        if(!repeated[i]) continue;
                        int h=(int)Math.Sqrt(n);
                        if((long)h*h==n && small[h]==false) continue;
                    }
                    if(repeated[i]) {
                        ++remaining;
                        log.WriteLine(n+" repeated");
                    } else {
                        ++accepted;
                        log.WriteLine(n+" squarefree");
                    }
                }
                lo=hi+1;
            }
        }
        Console.WriteLine("interval [{0},{1}], squarefree members {2}, prime-power tests needed {3}",start,end,accepted,remaining);
        return 0;
    }
}

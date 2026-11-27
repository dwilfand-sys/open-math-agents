using System;
using System.Collections.Generic;

// Count r and 2r-1 both prime in successive intervals above 10^10.
// For r>3 the pair forces r=6k+1, giving the other form 12k+1.
public class CunninghamMinusCounts
{
    static int[] Primes(int limit)
    {
        bool[] composite = new bool[limit + 1];
        var primes = new List<int>();
        for (int i = 2; i <= limit; ++i)
        {
            if (composite[i]) continue;
            primes.Add(i);
            if ((long)i * i <= limit)
                for (int j = i * i; j <= limit; j += i) composite[j] = true;
        }
        return primes.ToArray();
    }

    static int Root(int slope, int p)
    {
        // -slope^{-1} mod p, found via the small numerator m*p-1.
        for (int m = 1; m <= slope; ++m)
            if (((long)m * p - 1) % slope == 0) return (int)(((long)m * p - 1) / slope);
        throw new ArgumentException();
    }

    public static void Main(string[] args)
    {
        long lo = long.Parse(args[0]), hi = long.Parse(args[1]), step = long.Parse(args[2]);
        long root = (long)Math.Sqrt(2 * hi);
        while ((root+1)*(root+1) <= 2*hi) ++root;
        if (lo <= root || step<=0 || (hi-lo)%step!=0 || lo>hi) throw new ArgumentException();
        int[] primes = Array.FindAll(Primes((int)root), p => p>17);
        int[] six = new int[primes.Length], twelve = new int[primes.Length];
        for (int i=0; i<primes.Length; ++i)
        {
            six[i]=Root(6, primes[i]);
            twelve[i]=Root(12, primes[i]);
        }
        const int wheel=5*7*11*13*17;
        byte[] periodic = new byte[wheel];
        for (int k=0; k<wheel; ++k)
        {
            bool good=true;
            foreach (int p in new[] {5,7,11,13,17})
                if ((6*k+1)%p==0 || (12*k+1)%p==0) good=false;
            periodic[k]=(byte)(good?1:0);
        }
        const int blockSize=8*wheel;
        byte[] block = new byte[blockSize];
        for (long lower=lo; lower<hi; lower+=step)
        {
            long upper=lower+step;
            int count=0;
            long first=(lower-1)/6+1, end=(upper-1)/6+1;
            for (long start=first; start<end; start+=blockSize)
            {
                int length=(int)Math.Min((long)blockSize, end-start);
                int at=(int)(start%wheel), initial=Math.Min(wheel-at,length);
                Buffer.BlockCopy(periodic, at, block, 0, initial);
                for (int j=initial; j<length; j+=wheel)
                    Buffer.BlockCopy(periodic, 0, block, j, Math.Min(wheel,length-j));
                for (int i=0; i<primes.Length; ++i)
                {
                    int p=primes[i];
                    if ((long)p*p>12*(start+length-1)+1) break;
                    int rem=(int)(start%p);
                    int a=six[i]-rem, b=twelve[i]-rem;
                    if (a<0) a+=p;
                    if (b<0) b+=p;
                    for (int j=a; j<length; j+=p) block[j]=0;
                    for (int j=b; j<length; j+=p) block[j]=0;
                }
                for (int j=0; j<length; ++j) count+=block[j];
            }
            Console.WriteLine("{0} {1} {2}",lower,upper,count);
        }
    }
}

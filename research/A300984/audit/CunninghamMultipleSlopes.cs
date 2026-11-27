using System;
using System.Collections.Generic;
using System.Numerics;

// For every set of small negative slopes, certify the additional excluded
// negative high coordinates after its least slope has already been applied.
public class CunninghamMultipleSlopes
{
    static readonly int[] Slopes={5,11,17,23,29,41,47,53,59,71};
    const int Width=262144;
    const long Scale=1000000000000000;

    class Form
    {
        readonly int[] steps, next;
        public Form(int a, int b, long first, long end, List<int> primes)
        {
            var qs=new List<int>(); var offsets=new List<int>();
            long maximum=a*(end-1)+b;
            foreach(int q in primes)
            {
                if((long)q*q>maximum) break;
                if(a%q==0) continue;
                int u=0,v=1,x=q,y=a%q;
                while(y!=0)
                {
                    int k=x/y, r=x%y, w=u-k*v;
                    x=y; y=r; u=v; v=w;
                }
                long root=(-(long)b*u)%q;
                offsets.Add((int)((root-first%q+2L*q)%q)); qs.Add(q);
            }
            steps=qs.ToArray(); next=offsets.ToArray();
        }
        public void Mark(byte[] flags,int length)
        {
            Array.Clear(flags,0,length);
            for(int i=0;i<steps.Length;i++)
            {
                int j=next[i], step=steps[i];
                for(;j<length;j+=step) flags[j]=1;
                next[i]=j-length;
            }
        }
    }

    public static void Main(string[] args)
    {
        long lower=long.Parse(args[0]),upper=long.Parse(args[1]);
        if(lower<10000 || upper<=lower || upper>100000000000L) throw new ArgumentException();
        int cap=(int)Math.Sqrt(2L*Slopes[Slopes.Length-1]*upper)+1;
        if(lower<=cap) throw new ArgumentException();
        var primes=new List<int>(); var bad=new bool[cap+1];
        for(int q=2;q<=cap;q++) if(!bad[q])
        {
            primes.Add(q);
            if((long)q*q<=cap) for(int n=q*q;n<=cap;n+=q) bad[n]=true;
        }
        long first=(lower-5)/6+1,end=(upper-5)/6+1;
        var prime=new Form(6,5,first,end,primes);
        var forms=Array.ConvertAll(Slopes,s=>new Form(12*s,10*s-1,first,end,primes));
        int masks=1<<Slopes.Length;
        var totals=new long[masks]; var factors=new long[masks];
        for(int i=0;i<masks;i++) factors[i]=Scale;
        var pBad=new byte[Width]; var flags=new byte[Width];
        var signature=new ushort[Width]; var counts=new int[masks];
        for(long start=first;start<end;start+=Width)
        {
            int length=(int)Math.Min((long)Width,end-start);
            prime.Mark(pBad,length);
            Array.Clear(signature,0,length);
            for(int j=0;j<forms.Length;j++)
            {
                forms[j].Mark(flags,length);
                for(int i=0;i<length;i++) if(flags[i]!=0) signature[i]|=(ushort)(1<<j);
            }
            Array.Clear(counts,0,masks);
            for(int i=0;i<length;i++) if(pBad[i]==0)counts[signature[i]]++;
            for(int bit=1;bit<masks;bit*=2)
                for(int m=0;m<masks;m++) if((m&bit)==0) counts[m]+=counts[m|bit];
            long top=6*(start+length-1)+5;
            for(int m=1;m<masks;m++)
            {
                int n=counts[m&-m]-counts[m];
                if(n==0)continue;
                totals[m]+=n; long d=top+n;
                factors[m]=(long)(((BigInteger)factors[m]*top+d-1)/d);
            }
        }
        for(int m=0;m<masks;m++) Console.WriteLine("{0} {1} {2} {3} {4}",lower,upper,m,totals[m],factors[m]);
    }
}

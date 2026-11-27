using System;
using System.Collections.Generic;
using System.Numerics;

// For a selected small pair a,b, count previously unused high coordinates
// r with r and 2*a*b*r-1 prime. The table keeps every small-prime guard mask.
public class CunninghamCompositeSlopes
{
    const int Width=262144;
    const long Scale=1000000000000000L;
    static readonly int[] Negative={5,11,17,23,29,41,47,53,59,71};
    static readonly int[] Positive={13,43,61,67,73};
    static readonly int[,] Pairs={{5,13},{5,17},{11,13},{5,29},{5,43},{13,17},
      {5,47},{11,23},{5,53},{5,59},{13,23},{5,61},{11,29},{5,67},{5,73},{13,29},
      {17,23},{11,41},{11,43},{17,29},{13,41},{11,53},{13,47},{23,29}};

    static bool Prime(int n)
    {
        for(int d=2;d*d<=n;d++) if(n%d==0)return false;
        return n>=2;
    }

    class Sieve
    {
        readonly int[] primes,offsets;
        public Sieve(int a,int b,long first,long end,List<int> basePrimes)
        {
            var ps=new List<int>(); var os=new List<int>();
            foreach(int p in basePrimes)
            {
                if((long)p*p>(end-1)*a+b) break;
                if(a%p==0) {if(b%p==0)throw new ArgumentException(); continue;}
                long x=a%p,y=p,u=1,v=0;
                while(y>0) {
                    long q=x/y;
                    long z=x-q*y; x=y; y=z;
                    z=u-q*v; u=v; v=z;
                }
                long root=((-b*u-first)%p+p)%p;
                os.Add((int)root); ps.Add(p);
            }
            primes=ps.ToArray(); offsets=os.ToArray();
        }
        public void Mark(byte[] marks,int n)
        {
            Array.Clear(marks,0,n);
            for(int i=0;i<primes.Length;i++) {
                int j=offsets[i],p=primes[i];
                for(;j<n;j+=p) marks[j]=1;
                offsets[i]=j-n;
            }
        }
    }

    public static void Main(string[] args)
    {
        int sign=int.Parse(args[0]);
        long lower=long.Parse(args[1]),upper=long.Parse(args[2]);
        bool medium=lower>=14000000L && upper<=1000000000L;
        bool high=lower>=3000000000L && upper<=10000000000L;
        bool exactLow=lower>=50000L && upper<=14000000L;
        if((sign!=1&&sign!=5) || (!medium&&!high&&!exactLow) || upper<=lower)
            throw new ArgumentException();
        bool remaining=args.Length==4 && args[3]=="remaining";
        if(args.Length!=3 && !remaining)throw new ArgumentException();
        var candidates=new List<int[]>();
        if(remaining) {
            var smallPrimes=new List<int>(Negative);
            smallPrimes.AddRange(Positive);
            smallPrimes.Sort();
            for(int i=0;i<smallPrimes.Count;i++)for(int j=i+1;j<smallPrimes.Count;j++) {
                int a=smallPrimes[i],b=smallPrimes[j];
                bool present=false;
                for(int k=0;k<Pairs.GetLength(0);k++)
                    if(Pairs[k,0]==a && Pairs[k,1]==b)present=true;
                if(!present && !Prime(2*a*b-1))candidates.Add(new int[]{a,b});
            }
            if(candidates.Count!=60)throw new ArgumentException("Incomplete remaining pair list");
        } else for(int i=0;i<Pairs.GetLength(0);i++)candidates.Add(new int[]{Pairs[i,0],Pairs[i,1]});
        var pairs=new List<int[]>();
        int largest=1;
        foreach(var candidate in candidates) {
            int a=candidate[0],b=candidate[1],c=a*b;
            if(c%6!=sign)continue;
            pairs.Add(new int[]{a,b});
            largest=Math.Max(largest,c);
        }
        int cap=(int)Math.Sqrt(2L*largest*upper)+1;
        var primes=new List<int>(); var composite=new bool[cap+1];
        for(int p=2;p<=cap;p++)if(!composite[p]) {
            primes.Add(p);
            if((long)p*p<=cap)for(int k=p*p;k<=cap;k+=p)composite[k]=true;
        }
        long first=(lower-sign)/6+1,end=(upper-sign)/6+1;
        var rForm=new Sieve(6,sign,first,end,primes);
        var singleton=sign==1?new Sieve(12,1,first,end,primes):null;
        var small=sign==1?Positive:Negative;
        var guards=Array.ConvertAll(small,t=>new Sieve(12*t,2*sign*t-1,first,end,primes));
        var forms=pairs.ConvertAll(pair=> {
            int c=pair[0]*pair[1]; return new Sieve(12*c,2*sign*c-1,first,end,primes);
        }).ToArray();
        int cards=1<<small.Length;
        var needs=new int[forms.Length];
        for(int i=0;i<forms.Length;i++)
            foreach(int t in pairs[i]) {
                int at=Array.IndexOf(small,t);
                if(at>=0) needs[i]|=1<<at;
            }
        var counts=new long[forms.Length,cards]; var factors=new long[forms.Length,cards];
        for(int i=0;i<forms.Length;i++)for(int j=0;j<cards;j++)factors[i,j]=Scale;
        var rejected=new byte[Width]; var marks=new byte[Width]; var labels=new ushort[Width];
        var hist=new int[cards];
        for(long start=first;start<end;start+=Width) {
            int n=(int)Math.Min(Width,end-start);
            rForm.Mark(rejected,n);
            if(singleton!=null) {
                singleton.Mark(marks,n);
                for(int j=0;j<n;j++)if(marks[j]==0)rejected[j]=1;
            }
            Array.Clear(labels,0,n);
            for(int k=0;k<guards.Length;k++) {
                guards[k].Mark(marks,n);
                for(int j=0;j<n;j++)if(marks[j]!=0)labels[j]|=(ushort)(1<<k);
            }
            long top=6*(start+n-1)+sign;
            for(int i=0;i<forms.Length;i++) {
                forms[i].Mark(marks,n);
                Array.Clear(hist,0,cards);
                long c=pairs[i][0]*pairs[i][1];
                int firstUsable=0;
                if(exactLow)
                    while(firstUsable<n && c*(6*(start+firstUsable)+sign)<=20000000L) firstUsable++;
                for(int j=firstUsable;j<n;j++)if((marks[j]|rejected[j])==0)hist[labels[j]]++;
                for(int bit=1;bit<cards;bit*=2)for(int k=0;k<cards;k++)if((k&bit)==0)
                    hist[k]+=hist[k|bit];
                for(int k=needs[i];k<cards;k=(k+1)|needs[i]) {
                    int hits=hist[k];
                    counts[i,k]+=hits;
                    long den=top+hits;
                    factors[i,k]=(long)(((BigInteger)factors[i,k]*top+den-1)/den);
                }
            }
        }
        Console.WriteLine("# {0} {1} {2}{3}",sign,lower,upper,remaining?" remaining":"");
        for(int i=0;i<forms.Length;i++)for(int k=needs[i];k<cards;k=(k+1)|needs[i])
            Console.WriteLine("{0} {1} {2} {3} {4}",pairs[i][0],pairs[i][1],k,counts[i,k],factors[i,k]);
    }
}

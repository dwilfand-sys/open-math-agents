using System;
using System.Collections.Generic;
using System.Numerics;

// Compute, for each medium prime t=5 (mod 6), the r and 2tr-1 prime
// pairs with r=5 (mod 6) independently of a previous 2sr-1 test.
public class CunninghamConditionalStars
{
    const int Chunk=262144;
    static long Lower=14000000, Upper=1000000000;
    const long Scale=1000000000000000;
    static int[] Small={5,11,17,23,29,41,47,53,59,71};
    static int[] primes;
    static int FirstK,EndK;

    class Linear
    {
        int[] steps, next;
        public Linear(int a,int b)
        {
            var ps=new List<int>();
            var starts=new List<int>();
            long maximum=(long)a*(EndK-1)+b;
            foreach(int q in primes)
            {
                if ((long)q*q>maximum) break;
                if (a%q==0) continue;
                int u=0,v=1,x=q,y=a%q;
                while (y!=0)
                {
                    int h=x/y, z=x%y;
                    x=y; y=z;
                    int w=u-h*v; u=v; v=w;
                }
                long residue=(-(long)b*u)%q;
                if(residue<0) residue+=q;
                int offset=(int)((residue-FirstK)%q);
                if(offset<0) offset+=q;
                ps.Add(q); starts.Add(FirstK+offset);
            }
            steps=ps.ToArray(); next=starts.ToArray();
        }
        public void Mark(byte[] composite,int start,int length)
        {
            Array.Clear(composite,0,length);
            for(int i=0;i<steps.Length;i++)
            {
                int pos=next[i]-start, q=steps[i];
                for (;pos<length;pos+=q) composite[pos]=1;
                next[i]=start+pos;
            }
        }
    }

    public static void Main(string[] args)
    {
        int cap=int.Parse(args[0]);
        bool positive=args.Length>1 && args[1]=="positive";
        int centerMin=args.Length>2?int.Parse(args[2]):73;
        if(args.Length>3) Lower=long.Parse(args[3]);
        if(args.Length>4) Upper=long.Parse(args[4]);
        int multiplier=args.Length>5?int.Parse(args[5]):1;
        if(multiplier<=0 || multiplier>73 || multiplier%2==0 || multiplier%3==0) throw new ArgumentException();
        if(Lower<=0 || Upper<=Lower || Upper>10000000000L || cap<=centerMin) throw new ArgumentException();
        int residue=positive?1:5;
        if(positive) Small=new int[]{13,43,61,67,73};
        FirstK=checked((int)((Lower-residue)/6+1));
        EndK=checked((int)((Upper-residue)/6+1));
        if(cap<83 || cap>100000) throw new ArgumentException();
        int primeCap=(int)Math.Sqrt(2L*multiplier*cap*Upper)+1;
        if(Lower<=primeCap) throw new ArgumentException("Lower endpoint must exceed all trial factors");
        bool[] composite=new bool[primeCap+1];
        var pr=new List<int>();
        for(int p=2;p<=primeCap;p++) if(!composite[p])
        {
            pr.Add(p);
            if((long)p*p<=primeCap) for(int n=p*p;n<=primeCap;n+=p) composite[n]=true;
        }
        primes=pr.ToArray();
        int[] medium=Array.FindAll(primes,t=>t>centerMin && t<=cap && t*multiplier%6==residue
                                   && (t%6!=1 || composite[2*t-1]));
        var low=new Linear[Small.Length];
        for(int j=0;j<Small.Length;j++) low[j]=new Linear(12*Small[j],2*residue*Small[j]-1);
        var high=new Linear[medium.Length];
        for(int j=0;j<medium.Length;j++) high[j]=new Linear(12*multiplier*medium[j],2*residue*multiplier*medium[j]-1);
        var rSieve=new Linear(6,residue);
        var singleton=positive?new Linear(12,1):null;
        byte[] rComposite=new byte[Chunk], corr=new byte[Chunk];
        ushort[] labels=new ushort[Chunk];
        int[] hist=new int[1<<Small.Length];
        int columns=positive?(1<<Small.Length):Small.Length+1;
        long[,] counts=new long[medium.Length,columns];
        long[,] upperFactor=new long[medium.Length,columns];
        for(int j=0;j<medium.Length;j++) for(int i=0;i<columns;i++) upperFactor[j,i]=Scale;
        for(int start=FirstK;start<EndK;start+=Chunk)
        {
            int length=Math.Min(Chunk,EndK-start);
            rSieve.Mark(rComposite,start,length);
            if(positive)
            {
                singleton.Mark(corr,start,length);
                for(int i=0;i<length;i++) if(corr[i]==0) rComposite[i]=1;
            }
            Array.Clear(labels,0,length);
            for(int j=0;j<Small.Length;j++)
            {
                low[j].Mark(corr,start,length);
                for(int i=0;i<length;i++) if(corr[i]!=0) labels[i]|=(ushort)(1<<j);
            }
            long top=6L*(start+length-1)+residue;
            for(int j=0;j<medium.Length;j++)
            {
                high[j].Mark(corr,start,length);
                Array.Clear(hist,0,hist.Length);
                for(int i=0;i<length;i++) if((rComposite[i]|corr[i])==0) hist[labels[i]]++;
                int[] blockCounts=new int[columns];
                if(positive)
                {
                    Array.Copy(hist,blockCounts,hist.Length);
                    for(int jbit=1;jbit<columns;jbit*=2)
                        for(int mask=0;mask<columns;mask++)
                            if((mask&jbit)==0) blockCounts[mask]+=blockCounts[mask|jbit];
                }
                else for(int mask=0;mask<hist.Length;mask++)
                    {
                        int n=hist[mask];
                        if(n==0) continue;
                        blockCounts[0]+=n;
                        for(int i=0;i<Small.Length;i++) if((mask&(1<<i))!=0) blockCounts[i+1]+=n;
                    }
                for(int i=0;i<blockCounts.Length;i++)
                {
                    int n=blockCounts[i];
                    counts[j,i]+=n;
                    upperFactor[j,i]=(long)(((BigInteger)upperFactor[j,i]*top+top+n-1)/(top+n));
                }
            }
        }
        for(int j=0;j<medium.Length;j++) for(int i=0;i<columns;i++)
            Console.WriteLine("{0} {1} {2} {3}",medium[j],positive?i:(i==0?0:Small[i-1]),counts[j,i],upperFactor[j,i]);
    }
}

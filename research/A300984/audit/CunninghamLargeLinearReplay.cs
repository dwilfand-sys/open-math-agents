using System;
using System.Collections.Generic;
using System.Numerics;

// Independent block-exact replay of r,2*s*r-1 prime for r=5 (mod 6).
public class CunninghamLargeLinearReplay
{
    static long Inverse(int x,int m)
    {
        int a=x,b=m,u=1,v=0;
        while(b!=0)
        {
            int h=a/b,z=a%b; a=b; b=z;
            int w=u-h*v; u=v; v=w;
        }
        return a==1?(u%m+m)%m:-1;
    }
    static List<int> Primes(int bound)
    {
        bool[] bad=new bool[bound+1];
        var result=new List<int>();
        for(int p=2;p<=bound;p++) if(!bad[p])
        {
            result.Add(p);
            if((long)p*p<=bound) for(int n=p*p;n<=bound;n+=p) bad[n]=true;
        }
        return result;
    }
    static void AddProgressions(List<int> steps,List<int> offsets,List<int> primes,
                                int m,int c,long first,long last)
    {
        long lowValue=m*first+c,highValue=m*last+c;
        foreach(int q in primes)
        {
            if((long)q*q>highValue) break;
            if(q<=17) continue;
            long inv=Inverse(q,m);
            if(inv<0) {if(c%q==0) throw new ArgumentException(); continue;}
            long a=(lowValue+q-1)/q;
            long cofactor=a+((c*inv%m-a%m+m)%m);
            long k=(q*cofactor-c)/m;
            if(k<first || k>=first+q) throw new ArgumentException();
            steps.Add(q);
            offsets.Add((int)(k-first));
        }
    }
    static void Run(long lower,long upper,int slope)
    {
        const int blockSize=1048576,wheel=5*7*11*13*17;
        long first=(lower-5)/6+1,end=(upper-5)/6+1;
        int cap=(int)Math.Sqrt(2L*slope*upper)+1;
        if(lower<=cap)throw new ArgumentException();
        var primes=Primes(cap);
        var qs=new List<int>();var ns=new List<int>();
        AddProgressions(qs,ns,primes,6,5,first,end-1);
        AddProgressions(qs,ns,primes,12*slope,10*slope-1,first,end-1);
        int[] steps=qs.ToArray(),offsets=ns.ToArray();
        byte[] pattern=new byte[wheel],flags=new byte[blockSize];
        int[] small={5,7,11,13,17};
        for(int k=0;k<wheel;k++)
        {
            long r=6L*k+5,shift=2*slope*r-1;
            bool keep=true;
            foreach(int q in small) if(r%q==0 || shift%q==0)keep=false;
            pattern[k]=(byte)(keep?1:0);
        }
        long total=0, factor=1000000000000000L;
        int blocks=0;
        for(long start=first;start<end;start+=blockSize)
        {
            int length=(int)Math.Min((long)blockSize,end-start);
            int mov=(int)(start%wheel),initial=Math.Min(wheel-mov,length);
            Buffer.BlockCopy(pattern,mov,flags,0,initial);
            for(int j=initial;j<length;j+=wheel)Buffer.BlockCopy(pattern,0,flags,j,Math.Min(wheel,length-j));
            for(int i=0;i<steps.Length;i++)
            {
                int j=offsets[i],q=steps[i];
                for(;j<length;j+=q)flags[j]=0;
                offsets[i]=j-length;
            }
            int count=0;for(int j=0;j<length;j++)count+=flags[j];
            long hi=6*(start+length-1)+5,d=hi+count;
            factor=(long)(((BigInteger)factor*hi+d-1)/d);
            total+=count;blocks++;
        }
        Console.WriteLine("{0} {1} {2} {3}",slope,total,factor,blocks);
    }
    public static void Main(string[] args)
    {
        long lower=long.Parse(args[0]),upper=long.Parse(args[1]);
        for(int i=2;i<args.Length;i++)Run(lower,upper,int.Parse(args[i]));
    }
}

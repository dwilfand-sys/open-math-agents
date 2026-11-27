// Enumerate complete inside configurations by intersecting domains of A blocks.
// The binary input records all actual points on each block as primitive row IDs.
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics;

class CubeSearch {
    class Point {
        public int aMask;
        public int[] resources;
        public ulong low,high;
    }
    static Point[] points;
    static int[][][] blocks=new int[8][][];
    static int[][] seeds;
    static List<int>[] global=new List<int>[8];
    static ulong[][][][] matrix;
    static int[][][] work;
    static int[,] sizes;
    static int[] chosen=new int[8];
    static long[] counts=new long[9];
    static StreamWriter results;

    static void Read(string path) {
        using(var r=new BinaryReader(File.OpenRead(path))) {
            if(r.ReadInt32()!=73002) throw new InvalidDataException();
            points=new Point[r.ReadInt32()];
            for(int i=0;i<points.Length;i++){
                var pt=new Point();var lines=new List<int>();
                int na=r.ReadInt32();for(int j=0;j<na;j++){
                    int a=r.ReadInt32();pt.aMask|=1<<a;lines.Add(a);
                }
                int nb=r.ReadInt32();for(int j=0;j<nb;j++)lines.Add(8+r.ReadInt32());
                foreach(int k in lines){if(k<64)pt.low|=1UL<<k;else pt.high|=1UL<<(k-64);}
                var pairs=new List<int>();
                for(int x=0;x<lines.Count;x++)for(int y=x+1;y<lines.Count;y++)
                    pairs.Add(80*lines[x]+lines[y]);
                pt.resources=pairs.ToArray();points[i]=pt;
            }
            for(int a=0;a<8;a++){
                blocks[a]=new int[r.ReadInt32()][];
                for(int i=0;i<blocks[a].Length;i++){
                    blocks[a][i]=new int[7];
                    for(int j=0;j<7;j++)blocks[a][i][j]=r.ReadInt32();
                }
            }
            seeds=new int[r.ReadInt32()][];
            for(int i=0;i<seeds.Length;i++){
                r.ReadInt32();seeds[i]=new int[r.ReadInt32()];
                for(int j=0;j<seeds[i].Length;j++)seeds[i][j]=r.ReadInt32();
            }
            if(r.BaseStream.Position!=r.BaseStream.Length)throw new InvalidDataException();
        }
    }
    static bool Clashes(int x,int y){
        var a=points[x];var b=points[y];
        ulong lo=a.low&b.low, hi=a.high&b.high;
        return (lo!=0 && hi!=0) || (lo&(lo-1))!=0 || (hi&(hi-1))!=0;
    }
    static bool FitsSeed(int a,int[] block,int[] seed){
        foreach(int x in seed){
            if((points[x].aMask & (1<<a))!=0){
                if(Array.IndexOf(block,x)<0)return false;
            }else foreach(int y in block)if(Clashes(x,y))return false;
        }
        return true;
    }
    static void Prepare(int[] seed){
        for(int a=0;a<8;a++){
            global[a]=new List<int>();
            for(int i=0;i<blocks[a].Length;i++)
                if(FitsSeed(a,blocks[a][i],seed))global[a].Add(i);
        }
        matrix=new ulong[8][][][];
        for(int a=0;a<8;a++)matrix[a]=new ulong[8][][];
        for(int b=0;b<8;b++){
            int words=(global[b].Count+63)/64;
            var byPair=new ulong[6400][];
            var byPoint=new ulong[points.Length][];
            for(int i=0;i<global[b].Count;i++){
                foreach(int x in blocks[b][global[b][i]]){
                    if(byPoint[x]==null)byPoint[x]=new ulong[words];
                    byPoint[x][i>>6]|=1UL<<(i&63);
                    foreach(int r in points[x].resources){
                        if(byPair[r]==null)byPair[r]=new ulong[words];
                        byPair[r][i>>6]|=1UL<<(i&63);
                    }
                }
            }
            var accept=new ulong[points.Length][];
            for(int x=0;x<points.Length;x++){
                if((points[x].aMask&(1<<b))!=0){
                    accept[x]=byPoint[x]??new ulong[words];
                }else{
                    var mask=new ulong[words];
                    foreach(int r in points[x].resources){
                        var q=byPair[r];if(q==null)continue;
                        for(int w=0;w<words;w++)mask[w]|=q[w];
                    }
                    for(int w=0;w<words;w++)mask[w]=~mask[w];
                    accept[x]=mask;
                }
            }
            for(int a=0;a<8;a++)if(a!=b){
                var rows=new ulong[global[a].Count][];
                for(int i=0;i<rows.Length;i++){
                    int[] block=blocks[a][global[a][i]];
                    var t=new ulong[words];
                    var x0=accept[block[0]];var x1=accept[block[1]];var x2=accept[block[2]];
                    var x3=accept[block[3]];var x4=accept[block[4]];var x5=accept[block[5]];var x6=accept[block[6]];
                    for(int w=0;w<words;w++)t[w]=x0[w]&x1[w]&x2[w]&x3[w]&x4[w]&x5[w]&x6[w];
                    rows[i]=t;
                }
                matrix[a][b]=rows;
            }
        }
        work=new int[9][][];sizes=new int[9,8];
        for(int d=0;d<9;d++){
            work[d]=new int[8][];
            for(int a=0;a<8;a++)work[d][a]=new int[global[a].Count];
        }
        for(int a=0;a<8;a++){
            sizes[0,a]=global[a].Count;
            for(int i=0;i<global[a].Count;i++)work[0][a][i]=i;
        }
    }
    static void Visit(int d,int active){
        counts[d]++;
        if(active==0){results.WriteLine(string.Join(",",chosen));return;}
        int a=-1;
        for(int i=7;i>=0;i--)if((active&(1<<i))!=0 && (a<0 || sizes[d,i]<sizes[d,a]))a=i;
        int next=active^(1<<a);
        int[] neighbors=new int[7-d];
        int k=0;
        for(int b=0;b<8;b++)if((next&(1<<b))!=0){
            int j=k++;
            while(j>0 && sizes[d,neighbors[j-1]]>sizes[d,b]){
                neighbors[j]=neighbors[j-1];j--;
            }
            neighbors[j]=b;
        }
        for(int x=0;x<sizes[d,a];x++){
            int i=work[d][a][x];
            bool feasible=true;
            foreach(int b in neighbors){
                int cnt=0; var links=matrix[a][b][i];
                var input=work[d][b];var output=work[d+1][b];
                int n=sizes[d,b];
                for(int z=0;z<n;z++){
                    int v=input[z];
                    if((links[v>>6]&(1UL<<(v&63)))!=0)output[cnt++]=v;
                }
                sizes[d+1,b]=cnt;
                if(cnt==0){feasible=false;break;}
            }
            if(feasible){
                chosen[a]=global[a][i];Visit(d+1,next);
            }
        }
    }
    static void Main(string[] args){
        Read(args[0]);int start=int.Parse(args[1]),end=int.Parse(args[2]);
        for(int seed=start;seed<end;seed++){
            var watch=Stopwatch.StartNew();
            Prepare(seeds[seed]);Array.Clear(counts,0,counts.Length);
            Console.WriteLine("seed {0} domain sizes {1}",seed,string.Join(",",Array.ConvertAll(global,g=>g.Count)));
            string file=Path.Combine(args[3],string.Format("cube-seed-{0:d2}.txt",seed));
            using(results=new StreamWriter(file+".partial"))Visit(0,255);
            if(File.Exists(file))throw new IOException("Existing completed seed: "+file);
            File.Move(file+".partial",file);
            Console.WriteLine("seed {0} depths {1} elapsed {2:f1}s",seed,string.Join(",",counts),watch.Elapsed.TotalSeconds);
            matrix=null;GC.Collect();
        }
    }
}

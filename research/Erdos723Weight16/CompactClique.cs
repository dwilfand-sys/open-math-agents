using System;
using System.IO;

// Enumerate one member per colour. A binary input contains the eight
// domain sizes and all directed compatibility bitsets in row-major order.
public class CompactClique
{
    static readonly int[] sizes = new int[8];
    static readonly int[] words = new int[8];
    static readonly int[] chosen = new int[8];
    static readonly long[] visits = new long[9];
    static readonly ulong[][][] compat = new ulong[8][][];
    static readonly ulong[][][] layers = new ulong[9][][];
    static readonly int[][][] occupied = new int[9][][];
    static readonly int[,] occupiedCount = new int[9,8];
    static BinaryWriter output;

    static int PopCount(ulong x)
    {
        x -= (x >> 1) & 0x5555555555555555UL;
        x = (x & 0x3333333333333333UL) + ((x >> 2) & 0x3333333333333333UL);
        return (int)((((x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fUL) * 0x0101010101010101UL) >> 56);
    }

    static void Visit(int depth, int live, int a)
    {
        ++visits[depth];
        if (live == 0)
        {
            foreach (int c in chosen) output.Write(c);
            return;
        }
        int rest = live ^ (1 << a);
        ulong[][] old = layers[depth], next = layers[depth+1];
        for (int chunk=0; chunk<occupiedCount[depth,a]; ++chunk)
        {
            int u = occupied[depth][a][chunk];
            ulong v = old[a][u];
            while (v != 0)
            {
                ulong least = v & (0UL - v);
                int i = 64*u + PopCount(least-1);
                v ^= least;
                bool valid = true;
                int best = -1, bestSize = Int32.MaxValue;
                for (int b=0; b<8; ++b)
                {
                    if ((rest & (1<<b)) == 0) continue;
                    ulong[] row = compat[a][b];
                    ulong[] source = old[b], target = next[b];
                    int count = 0, numWords = 0, offset = i*words[b];
                    int[] oldWords = occupied[depth][b], nextWords = occupied[depth+1][b];
                    for (int m=0; m<occupiedCount[depth,b]; ++m)
                    {
                        int k = oldWords[m];
                        ulong common = source[k] & row[offset+k];
                        if (common != 0)
                        {
                            nextWords[numWords++] = k;
                            target[k] = common;
                            count += PopCount(common);
                        }
                    }
                    occupiedCount[depth+1,b] = numWords;
                    if (count == 0)
                    {
                        valid = false;
                        break;
                    }
                    // Prefer the largest colour number in a tie, matching the reference.
                    if (count <= bestSize) { best=b; bestSize=count; }
                }
                if (valid)
                {
                    chosen[a] = i;
                    Visit(depth+1,rest,best);
                }
            }
        }
    }

    public static void Main()
    {
        BinaryReader reader = new BinaryReader(Console.OpenStandardInput());
        output = new BinaryWriter(Console.OpenStandardOutput());
        int first=0;
        for (int a=0; a<8; ++a)
        {
            sizes[a] = reader.ReadInt32();
            words[a] = (sizes[a]+63)/64;
            if (sizes[a] <= sizes[first]) first = a;
        }
        for (int a=0; a<8; ++a)
        {
            compat[a] = new ulong[8][];
            for (int b=0; b<8; ++b)
            {
                if (a == b) continue;
                ulong[] arr = new ulong[sizes[a]*words[b]];
                for (int k=0; k<arr.Length; ++k) arr[k] = reader.ReadUInt64();
                compat[a][b] = arr;
            }
        }
        for (int d=0; d<=8; ++d)
        {
            layers[d] = new ulong[8][];
            occupied[d] = new int[8][];
            for (int a=0; a<8; ++a)
            {
                layers[d][a] = new ulong[words[a]];
                occupied[d][a] = new int[words[a]];
            }
        }
        for (int a=0; a<8; ++a)
        {
            occupiedCount[0,a]=words[a];
            for (int k=0;k<words[a];++k) occupied[0][a][k]=k;
            for (int i=0; i<sizes[a]; ++i)
                layers[0][a][i/64] |= 1UL<<(i%64);
        }
        Visit(0,255,first);
        output.Flush();
        Console.Error.WriteLine(String.Join(",",visits));
    }
}

"""Cross-check the compiled traversal on small graphs, including multiword and empty domains."""
import argparse
from pathlib import Path
import random

from compact_seed_domains import CompactSeed
from scales_independent_search import solve


def random_graph(sizes,rng):
    graph=object.__new__(CompactSeed)
    graph.indices=[list(range(n)) for n in sizes]
    graph.full=[(1 << n)-1 for n in sizes]
    graph.fixed=()
    graph.compat=[[None]*8 for _ in range(8)]
    for a in range(8):
        for b in range(a+1,8):
            rows=[0]*sizes[a]
            cols=[0]*sizes[b]
            for i in range(sizes[a]):
                for j in range(sizes[b]):
                    if rng.randrange(5):
                        rows[i] |= 1<<j
                        cols[j] |= 1<<i
            graph.compat[a][b],graph.compat[b][a]=rows,cols
    return graph


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('executable',type=Path)
    args=ap.parse_args()
    rng=random.Random(723)
    sizes=[[1]*8,[1,1,0,2,3,82,1,3],[65,1,2,3,134,2,3,2]]
    sizes.extend([[rng.randint(1,4) for _ in range(7)]+[rng.randint(65,175)] for _ in range(24)])
    leaves=0
    for counts in sizes:
        graph=random_graph(counts,rng)
        want,reference_counts=solve(graph,())
        got,actual_counts=graph.solve_compiled(args.executable)
        if want!=got or reference_counts!=actual_counts:
            raise ValueError('different assignments or search-node counts')
        leaves+=len(got)
    print(f'Exact agreement for {len(sizes)} test graphs and {leaves} full assignments.')

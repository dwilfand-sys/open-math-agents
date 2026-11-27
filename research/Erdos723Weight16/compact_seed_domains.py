"""Compress the row domains remaining after fixing a seed of double points."""
from functools import cache
from itertools import combinations
from collections import defaultdict
from struct import pack, iter_unpack
import subprocess

from scales_block_consistency import members


class CompactSeed:
    def __init__(self, graph, fixed):
        self.indices = [list(members(domain)) for domain in graph.initial_many(fixed)]
        self.full = [(1 << len(domain))-1 for domain in self.indices]
        self.compat = [[None]*8 for _ in range(8)]
        self.blocks = [[] for _ in range(8)]
        self.fixed = fixed
        all_pairs, all_points = [], []
        data = graph.point_data

        @cache
        def resources(p):
            j, m = data[p]
            lines = list(j) + [8+b for b in members(m)]
            return tuple(80*a+b for a,b in combinations(lines,2))

        for a, indices in enumerate(self.indices):
            incidence = defaultdict(int)
            points = defaultdict(int)
            for i, original in enumerate(indices):
                bit = 1 << i
                for p in graph.direct[a][original]:
                    points[p] |= bit
                    for r in resources(p):
                        incidence[r] |= bit
            all_pairs.append(incidence)
            all_points.append(points)

        @cache
        def forbidden(a, p):
            acc = 0
            for r in resources(p):
                acc |= all_pairs[a].get(r, 0)
            return acc

        for a, indices in enumerate(self.indices):
            for b in range(8):
                if a == b:
                    continue
                rows=[]
                for i in indices:
                    domain = self.full[b]
                    conflict = 0
                    for p in graph.direct[a][i]:
                        if b in data[p][0]:
                            domain &= all_points[b].get(p,0)
                        else:
                            conflict |= forbidden(b,p)
                    rows.append(domain & ~conflict)
                self.compat[a][b]=rows

    def initial_many(self, fixed):
        if fixed != self.fixed:
            raise ValueError('wrong doubles seed')
        return self.full

    def original(self, assignment):
        return tuple((a, self.indices[a][i]) for a,i in assignment)

    def solve_compiled(self, executable):
        sizes=[len(domain) for domain in self.indices]
        inputs=bytearray(pack('<8i',*sizes))
        for a in range(8):
            for b in range(8):
                if a == b:
                    continue
                size=8*((sizes[b]+63)//64)
                for row in self.compat[a][b]:
                    inputs.extend(row.to_bytes(size,'little'))
        run=subprocess.run([str(executable.resolve())],input=inputs,capture_output=True,check=True)
        sols=[tuple(enumerate(ids)) for ids in iter_unpack('<8i',run.stdout)]
        stats={i:n for i,n in enumerate(map(int,run.stderr.decode('ascii').strip().split(','))) if n}
        if len(sols)!=stats.get(8,0):
            raise ValueError('compiled terminal count disagrees with its records')
        return sols,stats

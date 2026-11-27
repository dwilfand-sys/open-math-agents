"""Lazy compatibility index using the actual line-pair resources of every point."""
from collections import defaultdict
from functools import cache, lru_cache
from itertools import combinations

from inside_blocks import bits, local_choices
from scales_block_consistency import members


class PairLookup:
    def __init__(self, entry, left, right):
        self.entry, self.left, self.right = entry, left, right

    def __getitem__(self, index):
        return self.entry(self.left, self.right, index)


class SparseBlockDomains:
    def __init__(self, case, cache_rows=65000):
        self.blocks = [[] for _ in range(8)]
        self.full = []
        self.direct = []
        self.point_id = {}
        self.point_data = []
        by_pair = []
        by_point = []

        def point_id(p):
            if p not in self.point_id:
                self.point_id[p] = len(self.point_data)
                self.point_data.append(p)
            return self.point_id[p]

        @cache
        def resources(p):
            j, m = self.point_data[p]
            lines = list(j) + [8+b for b in members(m)]
            return [80*a+b for a,b in combinations(lines,2)]

        for a in range(8):
            out = self.blocks[a]
            local_choices(case, a, lambda _, doubles, singles: out.append((tuple(doubles),tuple(singles))))
            self.full.append((1<<len(out))-1)
            size = (len(out)+7)//8
            idx = defaultdict(lambda: bytearray(size))
            point_idx = defaultdict(lambda: bytearray(size))
            labels = []
            for i,(doubles,singles) in enumerate(out):
                block = tuple(point_id(p) for p in doubles) + tuple(point_id(((a,),m)) for m in singles)
                labels.append(block)
                byte, shift = divmod(i,8)
                bit = 1 << shift
                for p in block:
                    point_idx[p][byte] |= bit
                    for q in resources(p):
                        idx[q][byte] |= bit
            self.direct.append(labels)
            by_pair.append({k:int.from_bytes(v,'little') for k,v in idx.items()})
            by_point.append({k:int.from_bytes(v,'little') for k,v in point_idx.items()})

        @cache
        def forbidden(a,p):
            mask=0
            for q in resources(p):
                mask |= by_pair[a].get(q,0)
            return mask

        @lru_cache(maxsize=cache_rows)
        def row(a,b,i):
            candidates=self.full[b]
            conflicts=0
            for p in self.direct[a][i]:
                if b in self.point_data[p][0]:
                    candidates &= by_point[b][p]
                else:
                    conflicts |= forbidden(b,p)
            return candidates & ~conflicts

        self.compat = [[PairLookup(row,a,b) if a!=b else None for b in range(8)] for a in range(8)]
        self.by_point = by_point
        self.forbidden = forbidden

    def initial(self, fixed):
        ds = self.full.copy()
        for j, matching in fixed:
            p = self.point_id[(j,bits(matching))]
            for a in range(8):
                if a in j:
                    ds[a] &= self.by_point[a][p]
                else:
                    ds[a] &= ~self.forbidden(a,p)
        return ds

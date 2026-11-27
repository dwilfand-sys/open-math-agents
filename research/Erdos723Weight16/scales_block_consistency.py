"""Pairwise consistency of complete A blocks with a fixed distinguished point."""
from collections import defaultdict
from functools import cache
from itertools import combinations

from scales_fixed_intersection import case_data, block_supports, orbit_representatives, compatible
from inside_blocks import bits


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


class BlockGraph:
    def __init__(self, case):
        self.blocks = block_supports(case)
        self.full = [(1 << len(group)) - 1 for group in self.blocks]
        all_pairs = []
        indexed = []
        labels = []

        @cache
        def pair_resources(mask):
            return tuple(case.bb_col[p] - 300 for p in combinations(members(mask), 2))

        for group in self.blocks:
            bb = [0] * 1980
            dbl = defaultdict(int)
            parts = []
            for r, (doubles, singles) in enumerate(group):
                bit = 1 << r
                groups = [(None, pair_resources(m)) for m in singles]
                for j, m in doubles:
                    dbl[j, m] |= bit
                    groups.append((j, pair_resources(m)))
                for _, pairs in groups:
                    for pair in pairs:
                        bb[pair] |= bit
                parts.append(groups)
            all_pairs.append(parts)
            indexed.append(bb)
            labels.append(dbl)

        self.compat = [[None] * 8 for _ in range(8)]
        possible = [defaultdict(list) for _ in range(8)]
        for a in range(8):
            for (j, m), domain in labels[a].items():
                possible[a][j].append((m, domain))
        for a, blocks in enumerate(self.blocks):
            for b in range(a + 1, 8):
                shared = (a, b) if (a, b) in case.dd_col else None
                for u, v in [(a, b), (b, a)]:
                    matrix = []
                    for r, (doubles, _) in enumerate(self.blocks[u]):
                        options = self.full[v] if shared is None else labels[v][shared, dict(doubles)[shared]]
                        # Two distinct double points can share a third A row h.
                        # Then their B sets must be disjoint even if h's block
                        # has not yet been selected.
                        for edge, matched in doubles:
                            h = edge[1] if edge[0] == u else edge[0]
                            if h == v:
                                continue
                            other = tuple(sorted((v, h)))
                            for alternate, domain in possible[v][other]:
                                if matched & alternate:
                                    options &= ~domain
                        conflict = 0
                        for j, pairs in all_pairs[u][r]:
                            if shared is not None and j == shared:
                                continue
                            for resource in pairs:
                                conflict |= indexed[v][resource]
                        matrix.append(options & ~conflict)
                    self.compat[u][v] = matrix

    def initial(self, j, m):
        candidate = (j, bits(m))
        return [bits(i for i, block in enumerate(group) if compatible(a, block, candidate))
                for a, group in enumerate(self.blocks)]

    def reduce(self, domains):
        while True:
            changed = False
            for a in sorted(range(8), key=lambda i: domains[i].bit_count()):
                old = domains[a]
                if not old:
                    return False
                others = sorted((b for b in range(8) if a != b), key=lambda i: domains[i].bit_count())
                for b in others:
                    partners = self.compat[a][b]
                    permitted = domains[b]
                    old = bits(i for i in members(old) if partners[i] & permitted)
                    if not old:
                        return False
                if old != domains[a]:
                    domains[a] = old
                    changed = True
            if not changed:
                return True


if __name__ == '__main__':
    case, group = case_data()
    reps = orbit_representatives(case, group)
    graph = BlockGraph(case)
    local = arc = removed_weight = 0
    survivors = []
    for i, ((j, m), weight) in enumerate(reps):
        domains = graph.initial(j, m)
        if all(domains):
            local += 1
        if graph.reduce(domains):
            arc += 1
            survivors.append((i, min(d.bit_count() for d in domains), j, m))
        else:
            removed_weight += weight
    print('orbits surviving', len(reps), '->', local, '->', arc,
          'total candidates excluded', removed_weight, flush=True)
    print('smallest surviving domains', sorted(survivors, key=lambda x:x[1])[:10])

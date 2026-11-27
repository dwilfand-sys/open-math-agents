"""Test the seven hidden B35 points against partial A-block assignments."""
from itertools import combinations

from inside_blocks import bits
from scales_fixed_intersection import case_data, block_supports, compatible
from scales_forced_doubles import two_cases, anchor_graph
from scales_block_consistency import members


class HiddenFactors:
    def __init__(self, case, fixed):
        edges = anchor_graph(case, fixed)
        self.edges = bits(edges)
        graph = []
        for m in case.matchings((1 << 16) - 1):
            if 35 not in m:
                continue
            rest = set(m) - {35}
            if rest <= edges:
                graph.append(bits(rest))
        self.matchings = graph
        self.containing = {e: bits(i for i, m in enumerate(graph) if m & (1 << e)) for e in edges}
        self.full = (1 << len(graph)) - 1
        self.conflicts = []
        for m in graph:
            conflict = 0
            for e in members(m):
                conflict |= self.containing[e]
            self.conflicts.append(conflict)
        self.avoids = {}

    def avoids_point(self, point):
        # Point is distinct from all hidden B35 points. Its B35 incidence,
        # if present, occurs at a forced double point and is handled separately.
        point &= self.edges
        if point not in self.avoids:
            conflict = 0
            for a, b in combinations(members(point), 2):
                conflict |= self.containing[a] & self.containing[b]
            self.avoids[point] = self.full & ~conflict
        return self.avoids[point]

    def block_filter(self, block):
        doubles, singles = block
        domain = self.full
        for p in [m for _, m in doubles] + list(singles):
            domain &= self.avoids_point(p)
        return domain

    def solve(self, domain, limit=None):
        count = 0

        def search(edges, allowed):
            nonlocal count
            count += 1
            if limit and count > limit:
                raise TimeoutError
            if not edges:
                return ()
            best = allowed
            for e in members(edges):
                c = allowed & self.containing[e]
                if c.bit_count() < best.bit_count():
                    best = c
                if best.bit_count() < 2:
                    break
            for i in members(best):
                ans = search(edges ^ self.matchings[i], allowed & ~self.conflicts[i])
                if ans is not None:
                    return (i,) + ans
            return None

        try:
            result = search(self.edges, domain)
            if result is not None:
                assert len(result) == 7 and sum(self.matchings[i] for i in result) == self.edges
            return 'SAT' if result is not None else 'UNSAT', count
        except TimeoutError:
            return 'UNKNOWN', count


if __name__ == '__main__':
    import argparse
    from collections import Counter
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--a', type=int, default=1)
    ap.add_argument('--first', type=int, default=20)
    ap.add_argument('--limit', type=int, default=100000)
    args = ap.parse_args()
    case, group = case_data()
    blocks = block_supports(case)
    for fixed, _ in two_cases(case, group).items():
        solver = HiddenFactors(case, fixed)
        candidates = [b for b in blocks[args.a] if all(compatible(args.a, b, (j, bits(m))) for j, m in fixed)]
        stats = Counter()
        nodes = []
        for i, block in enumerate(candidates[:args.first]):
            status, n = solver.solve(solver.block_filter(block), args.limit)
            nodes.append(n)
            stats[status] += 1
        print(f'fixed {fixed}, {len(solver.matchings)} hidden matching options; '
              f'{args.a=} {len(candidates)} valid A blocks; checked {dict(stats)}, maximum nodes {max(nodes)}', flush=True)

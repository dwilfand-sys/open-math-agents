"""Exhaustively test completions of explicit low-A block prefixes at the B35 anchor."""
from collections import Counter
from functools import reduce
from operator import and_
from random import Random

from inside_blocks import bits
from scales_fixed_intersection import case_data, compatible
from scales_forced_doubles import two_cases
from scales_block_consistency import BlockGraph, members
from scales_anchor_factors import HiddenFactors


class LowBlocks:
    def __init__(self, graph, case, fixed):
        self.graph = graph
        self.solver = HiddenFactors(case, fixed)
        self.domains = [bits(i for i, block in enumerate(group) if all(
            compatible(a, block, (j, bits(m))) for j, m in fixed))
            for a, group in enumerate(graph.blocks)]
        self.hidden = [[self.solver.block_filter(b) for b in blocks] for blocks in graph.blocks]

    def update(self, domains, a, i):
        return [None if v is None or b == a else v & self.graph.compat[a][b][i] for b, v in enumerate(domains)]

    def extend(self, selected, stop_after_solution=True, node_limit=30000):
        order = [1, 2, 5, 6]
        ds = self.domains.copy()
        allowed = self.solver.full
        for a, i in zip(order, selected):
            if not ds[a] & (1 << i):
                return {'invalid': 1}
            ds = self.update(ds, a, i)
            allowed &= self.hidden[a][i]
        stats = Counter()
        def visit(depth, ds, allowed):
            if depth == len(order):
                status, n = self.solver.solve(allowed, node_limit)
                stats[status] += 1
                stats['search_nodes'] += n
                return status == 'SAT'
            a = order[depth]
            for i in members(ds[a]):
                if visit(depth+1, self.update(ds, a, i), allowed & self.hidden[a][i]) and stop_after_solution:
                    return True
            return False
        visit(len(selected), ds, allowed)
        return stats


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--trials', type=int, default=250)
    ap.add_argument('--prefix-length', type=int, choices=[1, 2, 3], default=3)
    options = ap.parse_args()
    case, group = case_data()
    graph = BlockGraph(case)
    for number, fixed in enumerate(two_cases(case, group)):
        c = LowBlocks(graph, case, fixed)
        rng = Random(723)
        results = Counter()
        best = None
        start = list(members(c.domains[1]))
        trial_range = range(len(start)) if options.prefix_length == 1 else range(options.trials)
        for t in trial_range:
            ds = c.domains.copy()
            selected = []
            for a in [1, 2, 5][:options.prefix_length]:
                if not ds[a]:
                    break
                i = start[t] if options.prefix_length == 1 else rng.choice(list(members(ds[a])))
                selected.append(i)
                ds = c.update(ds, a, i)
            if len(selected) != options.prefix_length:
                continue
            stats = c.extend(selected)
            if stats.get('SAT'):
                results['SAT'] += 1
            elif stats.get('UNKNOWN'):
                results['UNKNOWN'] += 1
            elif not stats.get('UNSAT'):
                results['dead from blocks'] += 1
            else:
                results['all factor tests refuted'] += 1
                if best is None or stats['search_nodes'] < best[0]:
                    best = (stats['search_nodes'], selected, dict(stats))
        print(number, results, best, flush=True)

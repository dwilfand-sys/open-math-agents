"""Independently reconstruct the local blocks and their pair constraints."""
from collections import defaultdict
from functools import cache
from itertools import combinations

from inside_blocks import bits
from scales_block_consistency import BlockGraph, members
from scales_fixed_intersection import case_data


def block_points(a, block):
    double, single = block
    return tuple(sorted(tuple(double) + tuple(((a,), m) for m in single)))


def audit_domains(case, graph):
    candidates = [(j, bits(m)) for j, m in case.candidates() if j]
    for a in range(8):
        options = [(j, m) for j, m in candidates if a in j]
        types = [j for j in case.double_types if a in j]
        point_resources = [m | ((1 << (72 + types.index(j))) if len(j) == 2 else 0) for j, m in options]
        universe = 0
        by_key = defaultdict(list)
        for idx, mask in enumerate(point_resources):
            universe |= mask
            for pos in members(mask):
                by_key[pos].append(idx)
        found = set()
        def visit(remaining, selected):
            if not remaining:
                found.add(tuple(sorted(options[i] for i in selected)))
                return
            # Choose the least-populated uncovered resource. A chosen point
            # removes every B it contains and its double type when present.
            pos = min(members(remaining), key=lambda k: len(by_key[k]))
            for point in by_key[pos]:
                mask = point_resources[point]
                if mask & remaining == mask:
                    visit(remaining ^ mask, selected + (point,))
        visit(universe, ())
        expected = {block_points(a, block) for block in graph.blocks[a]}
        assert len(expected) == len(graph.blocks[a]) and found == expected, a
    print('Independent local exact cover reproduced all eight block domains.', flush=True)


def audit_compatibilities(case, graph):
    @cache
    def resources(point):
        j, m = point
        rows = list(j) + [8 + b for b in members(m)]
        return tuple(80 * x + y for x, y in combinations(rows, 2))
    label = []
    by_pair = []
    descriptions = []
    for a, group in enumerate(graph.blocks):
        group_desc = [block_points(a, block) for block in group]
        pair_indices = defaultdict(int)
        type_indices = defaultdict(int)
        for i, points in enumerate(group_desc):
            bit = 1 << i
            for p in points:
                for q in resources(p):
                    pair_indices[q] |= bit
                if len(p[0]) == 2:
                    type_indices[p] |= bit
        label.append(type_indices)
        by_pair.append(pair_indices)
        descriptions.append(group_desc)
    compared = 0
    for a in range(8):
        for b in range(8):
            if a == b:
                continue
            j = tuple(sorted((a, b)))
            for i, points in enumerate(descriptions[a]):
                okay = graph.full[b]
                clashes = 0
                for p in points:
                    if p[0] == j:
                        okay &= label[b][p]
                    else:
                        for q in resources(p):
                            clashes |= by_pair[b][q]
                assert graph.compat[a][b][i] == okay & ~clashes, (a,b,i)
            compared += len(descriptions[a]) * len(descriptions[b])
    print(f'All {compared} ordered compatibility entries agree with the direct row-pair encoding.', flush=True)


if __name__ == '__main__':
    c, _ = case_data()
    blocks = BlockGraph(c)
    audit_domains(c, blocks)
    audit_compatibilities(c, blocks)

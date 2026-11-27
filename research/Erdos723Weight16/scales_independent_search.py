"""Enumerate the eight-colour clique problem in a dynamic variable order."""
import argparse
from collections import Counter

from inside_blocks import bits
from scales_block_consistency import BlockGraph, members
from scales_fixed_intersection import case_data, compatible
from scales_forced_doubles import two_cases


def solve(blocks, fixed, first_limit=None, split_log=None):
    stats = Counter()
    solutions = []
    if hasattr(blocks, 'initial'):
        dom = dict(enumerate(blocks.initial(fixed)))
    else:
        dom = {a: bits(i for i, block in enumerate(opts) if all(
            compatible(a, block, (j, bits(m))) for j, m in fixed))
            for a, opts in enumerate(blocks.blocks)}

    def visit(domains, chosen):
        stats[len(chosen)] += 1
        if not domains:
            solutions.append(tuple(sorted(chosen)))
            return
        a = min(domains, key=lambda h: (domains[h].bit_count(), -h))
        if split_log is not None:
            split_log.append(a)
        possible = list(members(domains[a]))
        if not chosen and first_limit is not None:
            possible = possible[:first_limit]
        for i in possible:
            reduced = {}
            for b, d in domains.items():
                if b == a:
                    continue
                v = d & blocks.compat[a][b][i]
                if not v:
                    break
                reduced[b] = v
            else:
                visit(reduced, chosen + ((a, i),))
    visit(dom, ())
    return solutions, stats


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--first-limit', type=int)
    args = ap.parse_args()
    c, g = case_data()
    blocks = BlockGraph(c)
    for k, fixed in enumerate(two_cases(c, g)):
        solutions, counts = solve(blocks, fixed, args.first_limit)
        print(k, 'nodes by depth', dict(sorted(counts.items())), 'solutions', solutions, flush=True)

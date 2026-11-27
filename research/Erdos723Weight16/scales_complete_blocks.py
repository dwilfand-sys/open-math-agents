"""Complete all eight inside blocks, then exact-cover the 49 B35 partner lines."""
import argparse
import json
from collections import Counter
from pathlib import Path

from scales_block_consistency import BlockGraph, members
from scales_fixed_intersection import case_data
from scales_forced_doubles import two_cases
from scales_prefix_test import LowBlocks


def run(low, first=0, stop=None, records=None):
    geom, domain = low.graph.compat, low.domains
    stats = Counter()
    high = (0, 3, 4, 7)

    def finish(ds, chosen, hidden):
        if not ds:
            stats['complete_inside'] += 1
            outcome, n = low.solver.solve(hidden)
            stats[outcome] += 1
            stats['factor_nodes'] += n
            if records is not None:
                projected = sorted(((hidden & low.solver.containing[b]).bit_count(), b)
                                   for b in members(low.solver.edges))
                points = set()
                for a,i in chosen:
                    doubles, singles = low.graph.blocks[a][i]
                    points.update(doubles)
                    points.update(((a,), m) for m in singles)
                records.append({'block_indices': dict(sorted(chosen)),
                    'points': [[j, list(members(m))] for j,m in sorted(points)],
                    'permitted_hidden_matchings': hidden.bit_count(),
                    'uncovered_B_partners': [b for count,b in projected if count == 0],
                    'factor_status': outcome, 'factor_search_nodes': n})
            if outcome == 'SAT':
                print('FEASIBLE INSIDE AND ANCHOR', chosen, flush=True)
            return
        a = min(ds, key=lambda k: ds[k].bit_count())
        for i in members(ds[a]):
            nextds = {b: opts & geom[a][b][i] for b, opts in ds.items() if b != a}
            if all(nextds.values()):
                finish(nextds, chosen + [(a,i)], hidden & low.hidden[a][i])

    for t, x in enumerate(list(members(domain[1]))[first:stop]):
        at2 = domain[2] & geom[1][2][x]
        start5 = domain[5] & geom[1][5][x]
        start6 = domain[6] & geom[1][6][x]
        h1 = [domain[b] & geom[1][b][x] for b in high]
        for y in members(at2):
            at5 = start5 & geom[2][5][y]
            base6 = start6 & geom[2][6][y]
            h2 = [u & geom[2][b][y] for b, u in zip(high, h1)]
            if not all(h2):
                continue
            hmask2 = low.hidden[1][x] & low.hidden[2][y]
            for z in members(at5):
                at6 = base6 & geom[5][6][z]
                if not at6:
                    continue
                h3 = [u & geom[5][b][z] for b, u in zip(high, h2)]
                if not all(h3):
                    continue
                hmask3 = hmask2 & low.hidden[5][z]
                for w in members(at6):
                    ds = {b: u & geom[6][b][w] for b, u in zip(high, h3)}
                    if not all(ds.values()):
                        continue
                    stats['four_low_live'] += 1
                    finish(ds, [(1,x),(2,y),(5,z),(6,w)], hmask3 & low.hidden[6][w])
        stats['first_blocks'] += 1
        if (t+1) % 75 == 0:
            print('progress', first+t+1, dict(stats), flush=True)
    return stats


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case', type=int, choices=[0,1])
    ap.add_argument('--first', type=int, default=0)
    ap.add_argument('--stop', type=int)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    c,g = case_data()
    blocks = BlockGraph(c)
    record = {}
    for index, fixed in enumerate(two_cases(c,g)):
        if args.case is None or args.case == index:
            solutions = []
            result = run(LowBlocks(blocks,c,fixed), args.first, args.stop, solutions if args.output else None)
            print(index, result, flush=True)
            record[index] = {'fixed': fixed, 'counts': dict(result), 'inside': solutions}
            if args.output:
                args.output.write_text(json.dumps(record, separators=(',', ':')) + '\n', encoding='utf8')

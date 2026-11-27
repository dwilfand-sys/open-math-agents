"""Re-enumerate a word's interiors using literal line-pair domains and two-colour branching."""
import argparse
from pathlib import Path

from other_sparse_cases import seed_orbits
from scales_block_consistency import members
from sparse_block_domains import SparseBlockDomains
from sparse_records import read_records
from weight16_exact_cover import StartingCase, WORDS


def solutions(graph, fixed):
    def visit(domains, chosen):
        if not domains:
            yield tuple(sorted(chosen))
            return
        # Always fix a pair of colours together. A pair of compatible members
        # leaves the intersection of their two domains on every remaining row.
        a, b, *rest = sorted(domains, key=lambda k: (domains[k].bit_count(), k))
        for i in members(domains[a]):
            remaining = {c: domains[c] & graph.compat[a][c][i] for c in rest}
            if not all(remaining.values()):
                continue
            for j in members(domains[b] & graph.compat[a][b][i]):
                next_domains = {c: remaining[c] & graph.compat[b][c][j] for c in rest}
                if all(next_domains.values()):
                    yield from visit(next_domains, chosen + ((a,i),(b,j)))
    yield from visit(dict(enumerate(graph.initial_many(fixed))), ())


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('case', type=int, choices=range(6))
    ap.add_argument('records', type=Path)
    ap.add_argument('--row-cache', type=int, default=6000)
    ap.add_argument('--compact', action='store_true', help='renumber each individual seed domain')
    args=ap.parse_args()
    case=StartingCase(WORDS[args.case])
    records=read_records(args.records)
    labels=[tuple(j) for j,_ in records['0']['seed']]
    seeds, raw=seed_orbits(case,labels)
    if set(records) != set(map(str,range(len(seeds)))):
        raise ValueError('the stored search does not cover all seed orbits')
    graph=SparseBlockDomains(case,cache_rows=args.row_cache)
    counts=[]
    for k,(seed,orbit_size) in enumerate(seeds):
        record=records[str(k)]
        if tuple((tuple(j),tuple(m)) for j,m in record['seed'])!=seed or record['orbit_size']!=orbit_size:
            raise ValueError(f'wrong seed in record {k}')
        expected={tuple(tuple(x) for x in r['blocks']) for r in record['inside']}
        if args.compact:
            from compact_seed_domains import CompactSeed
            compact=CompactSeed(graph,seed)
            actual={compact.original(x) for x in solutions(compact,seed)}
        else:
            actual=set(solutions(graph,seed))
        if expected!=actual or len(expected)!=len(record['inside']):
            raise ValueError(f'interior discrepancy for seed {k}')
        counts.append(len(actual))
        print(f'seed {k}: {len(actual)} interiors',flush=True)
    print(f'{len(seeds)} seed orbits covering {raw} choices, {sum(counts)} canonical-seed interiors',flush=True)

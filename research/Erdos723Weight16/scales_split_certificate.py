"""Generate or replay an exhaustive split certificate for the scales inside blocks."""
import argparse
import base64
import json
from pathlib import Path
import zlib

from inside_blocks import bits
from scales_block_consistency import BlockGraph, members
from scales_fixed_intersection import case_data, compatible
from scales_forced_doubles import two_cases
from scales_independent_search import solve


def encode(split_log):
    return base64.b64encode(zlib.compress(split_log, 9)).decode('ascii')


def replay(graph, fixed, certificate, expected):
    splits = zlib.decompress(base64.b64decode(certificate, validate=True))
    next_split = iter(splits)
    leaves = set()
    # A partial assignment can be discarded exactly when an unassigned colour
    # has no option compatible with all already fixed blocks.
    root = {a: bits(i for i, block in enumerate(options) if all(
        compatible(a, block, (j,bits(m))) for j,m in fixed))
        for a, options in enumerate(graph.blocks)}
    def check(available, chosen):
        if not available:
            key = tuple(sorted(chosen))
            if key not in expected:
                raise ValueError(f'unrecorded complete assignment {key}')
            leaves.add(key)
            return
        a = next(next_split, None)
        if a not in available:
            raise ValueError('invalid split colour or truncated certificate')
        # The certificate chooses a colour only. Every option for that colour
        # is checked, including alternatives omitted by an untrusted producer.
        for i in members(available[a]):
            reduced = {b: d & graph.compat[a][b][i] for b,d in available.items() if b != a}
            if all(reduced.values()):
                check(reduced, chosen+((a,i),))
    check(root, ())
    if next(next_split, None) is not None or expected != leaves:
        raise ValueError('extra decisions or unmatched stored assignments')
    return len(splits), len(leaves)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--generate', action='store_true')
    args = ap.parse_args()
    base = Path(__file__).parent
    path = base/'Case4SplitCertificate.json'
    records = json.loads((base/'Case4InsideConfigurations.json').read_text(encoding='utf8'))
    c, group = case_data()
    graph = BlockGraph(c)
    certificates = {} if args.generate else json.loads(path.read_text(encoding='utf8'))
    for index, seed in enumerate(two_cases(c,group)):
        expected = {tuple(sorted((int(a),int(i)) for a,i in r['block_indices'].items()))
                    for r in records[str(index)]['inside']}
        if args.generate:
            log = bytearray()
            solutions,_ = solve(graph,seed,split_log=log)
            if set(solutions) != expected:
                raise ValueError('generator disagrees with stored inside records')
            certificates[str(index)] = encode(log)
        n, k = replay(graph, seed, certificates[str(index)], expected)
        print(f'Start {index}: {n} certified splits, {k} complete assignments.', flush=True)
    if args.generate:
        path.write_bytes((json.dumps(certificates,separators=(',',':'))+'\n').encode('ascii'))

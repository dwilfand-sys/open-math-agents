"""Check the two finite-relaxation witnesses using only Python integers."""
import argparse
import json
from itertools import permutations
from pathlib import Path

from weight16_exact_cover import StartingCase


def require(test, explanation):
    if not test:
        raise ValueError(explanation)


def graph_actions(case):
    edges = set(case.double_types)
    support_index = {edge: i for i, edge in enumerate(case.support)}
    for perm in permutations(range(8)):
        def image(edge):
            return tuple(sorted(perm[i] for i in edge))
        if not all(image(edge) in edges for edge in edges):
            continue
        ts = [support_index[image(edge)] for edge in case.support]
        tb = [case.line_index[tuple(sorted((ts[i], ts[j])))] for i, j in case.lines]
        yield perm, tb


def checked_cover_columns(case, j, m):
    j, m = tuple(j), tuple(m)
    require(j == tuple(sorted(set(j))) and all(0 <= a < 8 for a in j), 'invalid A incidence')
    require(len(j) <= 1 or j in case.dd_col, 'double A incidence outside cubic graph')
    require(m == tuple(sorted(set(m))) and all(0 <= b < 72 for b in m), 'invalid B incidence')
    remaining = sorted(i for i, edge in enumerate(case.support) if set(j).isdisjoint(edge))
    matched = sorted(i for b in m for i in case.lines[b])
    require(matched == remaining, 'witness does not give a perfect matching')
    return case.constraint_indices(j, m)


def verify(case, data):
    require(data['word'] == hex(case.word), 'incorrect canonical graph')
    weights = [0] * case.num_constraints
    actions = list(graph_actions(case))
    denominator = int(data['rational_denominator'])
    require(denominator > 0 and len(actions) == 16, 'bad scaling factor')
    for num, rows, matching in data['rational_orbit_points']:
        num = int(num)
        require(num > 0, 'nonpositive rational coefficient')
        for perm, line_perm in actions:
            j = sorted(perm[i] for i in rows)
            m = sorted(line_perm[b] for b in matching)
            for col in checked_cover_columns(case, j, m):
                weights[col] += num
    scale = denominator * len(actions)
    require(all(v == scale for v in weights), 'failed a rational exact-cover equation')
    require(sum(int(row[0]) for row in data['rational_orbit_points']) == 95 * denominator,
            'incorrect total rational weight')

    syndrome = 0
    for j, m in data['binary_points']:
        for c in checked_cover_columns(case, j, m):
            syndrome ^= 1 << c
    require(syndrome == (1 << case.num_constraints) - 1, 'failed a binary exact-cover equation')
    return len(actions), scale


def rank_and_binary_witness(case):
    pivots, combinations, candidates = {}, {}, []
    for j, m in case.candidates():
        original = sum(1 << c for c in case.constraint_indices(j, m))
        vector = original
        while vector and (key := vector.bit_length() - 1) in pivots:
            vector ^= pivots[key]
        if not vector:
            continue
        # Track row combinations only for the independent originals.
        key = vector.bit_length() - 1
        witness = 1 << len(candidates)
        reduced = original
        while (k := reduced.bit_length() - 1) in pivots:
            reduced ^= pivots[k]
            witness ^= combinations[k]
        pivots[key], combinations[key] = vector, witness
        candidates.append((j, m))
    rhs, answer = (1 << case.num_constraints) - 1, 0
    for key in sorted(pivots, reverse=True):
        if rhs & (1 << key):
            rhs ^= pivots[key]
            answer ^= combinations[key]
    require(rhs == 0, 'binary right-hand side is outside the span')
    return len(pivots), [row for i, row in enumerate(candidates) if (answer >> i) & 1]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank', action='store_true', help='also eliminate every candidate over GF(2)')
    options = parser.parse_args()
    case = StartingCase(0x3da1087)
    path = Path(__file__).with_name('Case4Relaxations.json')
    data = json.loads(path.read_text(encoding='utf8'))
    group_size, scale = verify(case, data)
    print(f'All {case.num_constraints} equations verified over the rationals and GF(2).')
    print(f'Rational witness: {len(data["rational_orbit_points"])} representatives, '
          f'group order {group_size}, common denominator {scale}.')
    print(f'Binary witness: {len(data["binary_points"])} candidates.')
    if options.rank:
        rank, _ = rank_and_binary_witness(case)
        require(rank == data['binary_rank'], 'reported rank differs from complete elimination')
        print(f'Full binary matrix rank: {rank}.')

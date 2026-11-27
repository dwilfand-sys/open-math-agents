"""A canonical two-case start from the exterior points A1/A2 and A5/A6."""
from itertools import product

from inside_blocks import bits
from scales_fixed_intersection import act, case_data, orbit_representatives


def two_cases(case, group):
    double_types = ((1, 2), (5, 6))
    options = []
    for j, tip in zip(double_types, ((0, 7), (3, 4))):
        remaining = [i for i, edge in enumerate(case.support) if set(j).isdisjoint(edge)]
        i = case.support.index(tip)
        neighbours = [k for k in remaining if set(tip).isdisjoint(case.support[k])]
        assert len(neighbours) == 1
        forced_line = case.line_index[tuple(sorted((i, neighbours[0])))]
        assert forced_line == 35
        options.append([(j, m) for m in case.matchings(bits(remaining))])
    assert [len(opts) for opts in options] == [3, 3]
    valid = set()
    for p, q in product(*options):
        if len(set(p[1]) & set(q[1])) == 1:
            valid.add((p, q))
    assert len(valid) == 8
    orbits = {}
    while valid:
        rep = min(valid)
        orbit = {tuple(sorted(act(v, p, b) for v in rep)) for p, b in group}
        assert orbit <= valid
        orbits[rep] = len(orbit)
        valid -= orbit
    assert sorted(orbits.values()) == [4, 4]
    return orbits


def coexist(u, v):
    if u == v:
        return True
    return len(set(u[0]) & set(v[0])) + len(set(u[1]) & set(v[1])) <= 1


def anchor_graph(case, double_points):
    b35 = set(case.lines[35])
    already_met = set.union(*(set(m) for _, m in double_points))
    edges = {b for b, endpoints in enumerate(case.lines) if b not in already_met and b35.isdisjoint(endpoints)}
    vertices = set(range(len(case.support))) - b35
    assert len(edges) == 49 and len(vertices) == 14
    assert all(sum(s in case.lines[b] for b in edges) == 7 for s in vertices)
    return edges


if __name__ == '__main__':
    case, group = case_data()
    reps = two_cases(case, group)
    all_intersections = [c for c in case.candidates() if 6 in c[1] and 35 in c[1]]
    allowed = set()
    for fixed, weight in reps.items():
        anchor_graph(case, fixed)
        possible = [p for p in all_intersections if all(coexist(p, q) for q in fixed)]
        allowed |= {act(c, p, b) for c in possible for p, b in group}
        print(f'fixed double points {fixed}, orbit size {weight}, '
              f'{len(possible)} compatible B6/B35 intersection candidates; '
              'B35 residual graph has degree 7 on 14 vertices.')
    orbit_counts = [(j, len(m), weight) for (j, m), weight in orbit_representatives(case, group)
                   if (j, m) in allowed]
    print(f'The two double points retain {len(allowed)} of 459 fixed-intersection candidates, '
          f'in {len(orbit_counts)} of 52 orbits.')

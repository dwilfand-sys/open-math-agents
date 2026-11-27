"""Orbit representatives of the mandatory exterior point on B6 and B35."""
from collections import Counter

from anchor_orbits import permutation_images, line_image
from inside_blocks import bits, local_choices
from weight16_exact_cover import StartingCase, WORDS


def case_data():
    case = StartingCase(WORDS[4])
    group = [(p, line_image(case, p)) for p in permutation_images(case)]
    return case, group


def act(candidate, p, b):
    j, m = candidate
    return tuple(sorted(p[i] for i in j)), tuple(sorted(b[i] for i in m))


def orbit_representatives(case, group, target=(6, 35)):
    fixed = [b for b in range(len(case.lines)) if all(g[b] == b for _, g in group)]
    assert fixed == [6, 35]
    remaining = {c for c in case.candidates() if all(b in c[1] for b in target)}
    original_size = len(remaining)
    representatives = []
    while remaining:
        rep = min(remaining)
        orbit = {act(rep, p, b) for p, b in group}
        assert orbit <= remaining
        remaining -= orbit
        representatives.append((rep, len(orbit)))
    assert sum(n for _, n in representatives) == original_size
    return representatives


def block_supports(case):
    blocks = [[] for _ in range(8)]

    def record(a, doubles, singles):
        blocks[a].append((tuple(doubles), tuple(singles)))

    for a in range(8):
        local_choices(case, a, record)
    return blocks


def compatible(a, block, candidate):
    doubles, singles = block
    j, m = candidate
    if a in j:
        if len(j) == 1:
            return m in singles
        return (j, m) in doubles
    return all((x & m).bit_count() <= 1 for x in singles) and all(
        (x & m).bit_count() + len(set(edge) & set(j)) <= 1 for edge, x in doubles)


if __name__ == '__main__':
    case, group = case_data()
    reps = orbit_representatives(case, group)
    blocks = block_supports(case)
    by_type = Counter()
    sizes = []
    for (j, m), orbit in reps:
        by_type[len(j), orbit] += 1
        choices = [sum(compatible(a, b, (j, bits(m))) for b in choices) for a, choices in enumerate(blocks)]
        sizes.append((min(choices), j, m, choices))
    print(f'{len(reps)} orbits of {sum(n for _, n in reps)} candidate points, by (|J|, orbit size):')
    print(sorted(by_type.items()))
    print('Smallest remaining single-block domains after fixing the intersection:')
    for row in sorted(sizes)[:8]:
        print(row)

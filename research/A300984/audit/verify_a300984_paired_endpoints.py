"""Bound the A300984 majority fraction using disjoint Cunningham-pair counts."""

from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations
from math import ceil, factorial
from pathlib import Path

from check_a300984_published_singletons import reciprocal_lower


PUBLISHED = {
    10: 26_571_998,
    11: 218_134_071,
    12: 1_822_880_701,
    13: 15_462_635_138,
    14: 132_822_560_771,
    15: 1_153_300_861_300,
}
PRIOR_24_PAIRS = Fraction(506_227_866_783_201, 10**15)
GRID = 10**18


def load_cells(path, cutoff):
    cells = [tuple(map(int, line.split())) for line in path.read_text().splitlines()]
    assert cells and all(len(cell) == 3 for cell in cells)
    assert all(lo < hi and 0 <= count <= hi - lo for lo, hi, count in cells)
    assert all(b <= c for (_, b, _), (c, _, _) in zip(cells, cells[1:]))
    assert all(not (lo < 10**12 < hi) for lo, hi, _ in cells)
    assert all(not (lo < cutoff < hi) for lo, hi, _ in cells)
    lower = [cell for cell in cells if cell[1] <= 10**12]
    upper = [cell for cell in cells if 10**12 <= cell[0] < cutoff]
    for block in (lower, upper):
        assert block and all(b == c for (_, b, _), (c, _, _) in zip(block, block[1:]))
    assert lower[0][0] == 10**10 and upper[0][0] == 10**12
    assert upper[-1][1] == cutoff and cutoff < 10**13
    assert sum(n for lo, hi, n in lower if hi <= 10**11) == PUBLISHED[11] - PUBLISHED[10]
    return lower, upper


def additional_mass(count, endpoint):
    assert count >= 0
    return int(GRID * reciprocal_lower(endpoint, count))


def bound(lower, upper, endpoints, prior):
    mass = sum(additional_mass(n, hi) for _, hi, n in lower + upper)
    low_residual = PUBLISHED[12] - PUBLISHED[10] - sum(n for _, _, n in lower)
    mass += additional_mass(low_residual, 10**12)
    used = PUBLISHED[12] + sum(n for _, _, n in upper)
    for exponent in endpoints:
        mass += additional_mass(PUBLISHED[exponent] - used, 10**exponent)
        used = PUBLISHED[exponent]
    h = Fraction(mass, GRID)
    exponential_lower = sum(h**j / factorial(j) for j in range(6))
    return mass, ceil(10**12 * prior / exponential_lower)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("bins", type=Path)
    parser.add_argument("--through", type=int, required=True)
    parser.add_argument("--prior-numerator", type=int, default=PRIOR_24_PAIRS.numerator)
    parser.add_argument("--prior-denominator", type=int, default=PRIOR_24_PAIRS.denominator)
    args = parser.parse_args()
    lower, upper = load_cells(args.bins, args.through)
    prior = Fraction(args.prior_numerator, args.prior_denominator)
    assert 0 < prior < 1
    print(f"{len(lower)} low cells and {len(upper)} high cells, through {args.through}")
    for size in range(4):
        for endpoints in combinations((13, 14, 15), size):
            mass, ratio = bound(lower, upper, endpoints, prior)
            print(f"{endpoints}: reciprocal mass >= {mass}/10^18; share <= {ratio}/10^12")

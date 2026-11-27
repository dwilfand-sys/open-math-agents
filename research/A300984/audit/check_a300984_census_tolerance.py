"""Stress-test the three external A300984 census totals using exact arithmetic."""

from functools import cache
from fractions import Fraction
from math import factorial
from pathlib import Path

from check_a300984_decade_subsets import LEVELS
from check_a300984_published_singletons import COUNTS, reciprocal_lower
from lagneau_selberg_packing import combined_mass, coefficient_intervals, packed_mass


PRIOR = Fraction(506227866783201, 10**15)
WINDOWS = (
    "CunninghamMinus10To100B.txt",
    "CunninghamMinus100To200B.txt",
    "CunninghamMinus200To400B.txt",
    "CunninghamMinus400To500B.txt",
    "CunninghamMinus1Tto1030B.txt",
)
GRID = 10**15


def prepare():
    root = Path(__file__).resolve().parent
    cells = sorted(tuple(map(int, row.split())) for name in WINDOWS
                   for row in (root/name).read_text(encoding="ascii").splitlines())
    assert all(a < b and n >= 0 for a, b, n in cells)
    assert all(b <= c for (_, b, _), (c, _, _) in zip(cells, cells[1:]))
    bins = []
    for lo in range(10, 15):
        rows = [(hi, count) for a, hi, count in cells if 10**lo <= a < hi <= 10**(lo+1)]
        bins.append((sum(c for _, c in rows), sum(reciprocal_lower(b, c) for b, c in rows)))
    stats = coefficient_intervals(LEVELS)

    @cache
    def maximum(hi, n, wheel_only):
        if wheel_only:
            return reciprocal_lower(hi, n)
        return max(reciprocal_lower(hi, n), combined_mass(hi, n, stats),
                   *(packed_mass(hi, n, level) for level in stats.values()))

    def lower_counts(eps):
        # Outward rounding deliberately widens the interval of integer counts.
        delta = [0, 0, 0] + [(eps*c).__ceil__() for c in COUNTS[3:]]
        return [max(known, COUNTS[i+1]-delta[i+1] - (COUNTS[i]+delta[i]))
                for i, (known, _) in enumerate(bins)]

    @cache
    def evaluate(eps, wheel_only=False):
        mass = Fraction(0)
        for i, ((known, fine), lower) in enumerate(zip(bins, lower_counts(eps))):
            hi = 10**(i+11)
            mass += max(fine+maximum(hi, lower-known, wheel_only),
                        maximum(hi, lower, wheel_only))
        return PRIOR / sum(mass**j/factorial(j) for j in range(6))

    def rank_widths(n):
        first_ranks = [int(1/g+(k/g)**2)+1 for g, k in stats.values()]
        return [(n+127)//128] + [max(0, (n-first+128)//128) for first in first_ranks]

    def same_partitions(left, right):
        for (known, _), before, after in zip(bins, lower_counts(left), lower_counts(right)):
            for offset in {0, known}:
                assert rank_widths(before-offset) == rank_widths(after-offset)

    return evaluate, same_partitions


def main():
    evaluate, same_partitions = prepare()
    for percent in map(Fraction, ('0', '1', '2', '3', '4', '5', '8', '8.8', '8.82', '10')):
        eps = percent/100
        outputs = [(evaluate(eps, wheel)*10**15).__ceil__() for wheel in (False, True)]
        print(percent, "percent; upper ratio / 10^15, packing then wheel", *outputs, flush=True)

    low, high = 0, GRID//2
    assert evaluate(Fraction(low, GRID)) < Fraction(1, 2) <= evaluate(Fraction(high, GRID))
    while high-low > 1:
        middle = (low+high)//2
        if evaluate(Fraction(middle, GRID)) < Fraction(1, 2):
            low = middle
        else:
            high = middle
    left, right = Fraction(low, GRID), Fraction(high, GRID)
    # An integer ceiling changes immediately to the right of k/C. Identify the
    # exact adjacent certified and uncertified configurations inside the bracket.
    breaks = {Fraction((left*c).__ceil__(), c) for c in COUNTS[3:]}
    breaks = sorted(x for x in breaks if left <= x < right)
    for i, point in enumerate(breaks):
        after = (point + (breaks[i+1] if i+1 < len(breaks) else right))/2
        at, following = evaluate(point), evaluate(after)
        if at < Fraction(1, 2) <= following:
            # Fix these exact rank partitions for a monotone certificate.
            # A larger lower count can discard the extra ranks. For a smaller
            # count truncate fixed rank groups. For each level the certified
            # distance increases with rank, so the mean distance in any
            # truncated group and its Jensen mass increase with the count.
            # Each maximizing choice therefore remains monotone. Unchanged
            # widths ensure the two computed endpoint results are exact for
            # this same frozen-partition test. Both bracket the last success.
            same_partitions(point, after)
            print("transition epsilon =", point, "; percent =", float(100*point))
            print("outward upper ratio at and immediately above, / 10^24:",
                  (at*10**24).__ceil__(), (following*10**24).__ceil__())
            return
    raise AssertionError("No adjacent transition in the bracket")


if __name__ == "__main__":
    main()

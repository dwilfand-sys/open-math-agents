"""Apply the A300984 packing bound with only 90% lower cumulative counts.

Reserve the known-window pairs. Among unreserved pairs above 10^10, the
number through each endpoint is at least its lower cumulative count minus the
verified initial count and the number reserved through that endpoint. These
integer quotas increase. Choose disjoint successive batches meeting their
differences in endpoint order, carrying unused early pairs forward. Add the
known-window pairs for the current decade to each batch. All its members are
at most its right endpoint. The rank packing proof needs just that upper bound
and the fact that all primes exceed its selected sieve level.
"""

from fractions import Fraction
from math import factorial
from pathlib import Path

from check_a300984_census_tolerance import COUNTS, LEVELS, PRIOR, WINDOWS
from lagneau_selberg_packing import coefficient_intervals, combined_mass, packed_mass, reciprocal_lower


def verify():
    levels = coefficient_intervals(LEVELS)
    data = Path(__file__).resolve().parent
    windows = sorted(tuple(map(int, line.split())) for name in WINDOWS
                     for line in (data/name).read_text(encoding="ascii").splitlines())
    assert all(a < b and count >= 0 for a, b, count in windows)
    assert all(b <= c for (_, b, _), (c, _, _) in zip(windows, windows[1:]))
    lower = list(COUNTS[:3]) + [9*c//10 for c in COUNTS[3:]]
    mass = Fraction()
    for i, (l, u) in enumerate(zip(lower, lower[1:])):
        left, right = 10**(i+10), 10**(i+11)
        cells = [(b, c) for a, b, c in windows if left <= a < b <= right]
        fixed = sum(c for _, c in cells)
        fine = sum(reciprocal_lower(b, c) for b, c in cells)
        total = u-l
        assert total >= fixed

        def pack(n):
            return max(reciprocal_lower(right, n), combined_mass(right, n, levels),
                       *(packed_mass(right, n, value) for value in levels.values()))

        mass += max(fine+pack(total-fixed), pack(total))
    answer = PRIOR/sum(mass**j/factorial(j) for j in range(6))
    assert answer < Fraction(1, 2)
    print("cumulative lower counts through 10^13, 10^14, 10^15:", lower[3:])
    print("outward upper ratio / 10^15:", (answer*10**15).__ceil__())


if __name__ == "__main__":
    verify()

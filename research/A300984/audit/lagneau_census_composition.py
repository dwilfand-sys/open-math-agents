"""Combine finer prime-pair bins and independently extended conditional slopes."""

from argparse import ArgumentParser
from fractions import Fraction
from math import factorial
from pathlib import Path

from check_a300984_published_singletons import COUNTS, reciprocal_lower


def count_windows(paths, before_census):
    decades = {}
    for path in paths:
        for line in path.read_text().splitlines():
            lo, hi, count = map(int, line.split())
            power = len(str(lo))
            assert 11 <= power <= 15 and 10**(power-1) <= lo < hi <= 10**power
            decades.setdefault(power, []).append((lo, hi, count))
    h = Fraction()
    for power, (before, after) in enumerate(zip(COUNTS, COUNTS[1:]), 11):
        current = 10**(power-1)
        remaining = after-before
        fine = Fraction()
        for lo, hi, count in sorted(decades.get(power, [])):
            assert lo == current and count >= 0
            remaining -= count
            fine += reciprocal_lower(hi, count)
            current = hi
        assert remaining >= 0 and (current != 10**power or remaining==0)
        h += max(reciprocal_lower(10**power,after-before),fine+reciprocal_lower(10**power,remaining))
    result = before_census / sum(h**j / factorial(j) for j in range(6))
    return h, result


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('before_census', type=int, help='upper ratio in units of 10^-15')
    parser.add_argument('windows', type=Path, nargs='+')
    args = parser.parse_args()
    h, result = count_windows(args.windows, Fraction(args.before_census,10**15))
    print('Reciprocal mass at least', (10**12*h).__floor__(), '/ 10^12.')
    print('Limiting ratio at most', (10**12*result).__ceil__(), '/ 10^12.')

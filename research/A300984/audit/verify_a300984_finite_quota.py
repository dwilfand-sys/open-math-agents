"""Derive sufficient finite Cunningham-pair counts from the archived A300984 bound."""
from argparse import ArgumentParser
from fractions import Fraction
from math import factorial
from pathlib import Path

from verify_a300984_paired_endpoints import GRID, bound, load_cells

PRIOR = Fraction(506_110_650_178_735, 10**15)
WINDOW = 10**9
LAST_FROZEN_ENDPOINT = 1_566_000_000_000


def ensures_strict_minority(mass_units):
    mass = Fraction(mass_units, GRID)
    return sum(mass**i / factorial(i) for i in range(6)) > 2 * PRIOR


def minimum_mass(current):
    low, high = current, GRID
    assert not ensures_strict_minority(low) and ensures_strict_minority(high)
    while high - low > 1:
        mid = (high + low) // 2
        if ensures_strict_minority(mid):
            high = mid
        else:
            low = mid
    return high


def sufficient_end(start, initial_mass, target, pairs_per_window):
    endpoint, mass = start, initial_mass
    while mass < target:
        previous = mass
        endpoint += WINDOW
        mass += pairs_per_window * GRID // endpoint
    assert previous < target <= mass
    return endpoint, mass


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("bins", type=Path)
    args = parser.parse_args()
    lower, upper = load_cells(args.bins, LAST_FROZEN_ENDPOINT)
    initial, _ = bound(lower, upper, (), PRIOR)
    target = minimum_mass(initial)
    print(f"Mass in units of 10^-18: archived {initial}, sufficient {target}")
    for quota in (1_300_000, 1_400_000, 1_450_000, 1_500_000):
        end, mass = sufficient_end(LAST_FROZEN_ENDPOINT, initial, target, quota)
        total = (end - LAST_FROZEN_ENDPOINT) // WINDOW
        print(f"{quota} pairs per billion: {total} windows through {end}; mass {mass}")

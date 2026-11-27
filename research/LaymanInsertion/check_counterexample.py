"""Exact checks for the explicit golden-rotation parameter in the Layman note."""
from fractions import Fraction as Q
from math import isqrt


def floor_multiple(n):
    return (isqrt(5 * n * n) - n) // 2


def parameter_interval(depth):
    lo, hi = Q(0), Q(1)
    for j in range(depth, 0, -1):
        digit = 3 + floor_multiple(j + 1) - floor_multiple(j)
        lo, hi = 1 / (digit - lo), 1 / (digit - hi)
    return 1 / (3 - lo), 1 / (3 - hi)


def active(x, y, bounds):
    lo, hi = bounds
    if x * hi.denominator >= y * hi.numerator:
        return True
    if x * lo.denominator < y * lo.numerator:
        return False
    raise ArithmeticError("Increase the exact enclosure depth")


def simultaneous_prefix(size, bounds):
    row = [1, 1]
    for step in range(1, 10 * size + 1):
        next_row = []
        for x, y in zip(row, row[1:]):
            next_row.append(x)
            if active(x, y, bounds):
                next_row.append(x + y)
            if len(next_row) >= size:
                break
        else:
            next_row.append(row[-1])
        row = next_row[:size]
        if len(row) == size and all(not active(x, y, bounds)
                                     for x, y in zip(row, row[1:])):
            return row, step
    raise ArithmeticError("Prefix has not stabilized")


def main():
    size = 512
    bounds = parameter_interval(2 * size)
    lo, hi = bounds
    assert 0 < hi - lo < Q(1, 10**600)
    row, rounds = simultaneous_prefix(size, bounds)
    before = 0
    high = 0
    for n, (x, y) in enumerate(zip(row, row[1:]), 1):
        digit, rem = divmod(y + before, x)
        assert rem == 0 and digit in (3, 4)
        assert active(x, y - x, bounds) and not active(x, y, bounds)
        high += digit - 3
        assert high == floor_multiple(n)
        before = x
    print(f"{size} stable terms in {rounds} simultaneous rounds; {high} high digits")
    print("First twelve terms:", row[:12])
    print(f"k = {float(lo):.15f} to displayed precision")


if __name__ == "__main__":
    main()

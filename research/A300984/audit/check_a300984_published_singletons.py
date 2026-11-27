"""Outward rational bounds using A401624 and optional exact first-decade bins."""

from fractions import Fraction
from math import factorial
from pathlib import Path
from sys import argv


# A401624, rows 10..15, values at consecutive powers of ten.
COUNTS = (26_571_998, 218_134_071, 1_822_880_701, 15_462_635_138,
          132_822_560_771, 1_153_300_861_300)
WHEEL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
PRIOR_UPPER = Fraction(512190165933052, 10**15)


def reciprocal_lower(upper, count):
    """Jensen bound from capacity of a full wheel in any translated interval."""
    if count == 0:
        return Fraction(0)
    lower = Fraction(count, upper)
    modulus = classes = 1
    for q in WHEEL_PRIMES:
        modulus *= q
        classes *= 1 if q == 2 else q - 2
        if classes > count:
            break
        blocks, leftover = divmod(count, classes)
        # Starting from upper, each length-modulus block can hold at most
        # 'classes' candidates r and 2r-1 both prime (all r exceed 43).
        distance = modulus * (classes * blocks * (blocks - 1) // 2 + leftover * blocks)
        lower = max(lower, Fraction(count**2, count * upper - distance))
    return lower


def lower_mass(path=None):
    sums = []
    for exponent, (left, right) in enumerate(zip(COUNTS, COUNTS[1:]), 11):
        sums.append(reciprocal_lower(10**exponent, right-left))
    if path is not None:
        known = 0
        covered = 10**10
        fine = Fraction(0)
        for line in Path(path).read_text(encoding="ascii").splitlines():
            lo, hi, count = map(int, line.split())
            assert lo == covered < hi <= 10**11 and count >= 0
            fine += reciprocal_lower(hi, count)
            covered, known = hi, known + count
        residual = COUNTS[1]-COUNTS[0]-known
        assert residual >= 0 and (covered != 10**11 or residual == 0)
        sums[0] = max(sums[0], fine + reciprocal_lower(10**11, residual))
    return sum(sums)


if __name__ == "__main__":
    h = lower_mass(argv[1] if len(argv)>1 else None)
    # Each newly excluded coordinate has weight at least 1/r. The exponential
    # here is rounded upward using a positive Taylor sum for exp(h).
    answer = PRIOR_UPPER / sum(h**j / factorial(j) for j in range(6))
    scale = 10**12
    print("reciprocal sum >=", (h * scale).__floor__(), "/ 10^12")
    print("limiting share <=", (answer * scale).__ceil__(), "/ 10^12")

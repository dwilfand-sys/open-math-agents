"""Exact arithmetic checks of the A085263 paper proof and initial OEIS data."""

from collections import Counter
from fractions import Fraction
from math import isqrt


def test_rational_bounds():
    q = Fraction
    cases = [
        (q(36, 125), q(1, 4), 22000 + q(1, 4), 64),
        (q(34, 125), q(1, 4), 22000 + q(1, 4), 128),
        (q(1, 4), q(2, 9), 262145 + q(2, 9), 512),
    ]
    for coefficient, prime_slope, prime_constant, rank_factor in cases:
        assert coefficient - prime_slope - q(1, 128) > q(1, 100)
        assert prime_constant + 61 * rank_factor < 300000
    assert q(87, 50) - q(8, 5) - q(1, 16) - q(1, 100) == q(27, 400)
    for rank in range(10, 181):
        assert 8**rank >= 4*rank
        minimal_j = 4*rank*8**rank
        for level in (0, 1, rank - 1, rank, rank + 1, 2*rank, 10**5):
            j = max(minimal_j, 15*level**2 + 1)
            assert 27*j > 400*rank*level
    print("Exact small-rank slopes, loss constants, large-rank constants, and "
          "1,197 parameter cases passed.")


def test_conjecture_data(limit=10000):
    # Mark squarefree numbers using every square divisor; primality is unnecessary.
    sf = bytearray([1]) * (limit + 1)
    sf[0] = 0
    for divisor in range(2, isqrt(limit) + 1):
        square = divisor**2
        sf[square::square] = bytes(limit // square)
    counts = [0] * (limit + 1)
    for root in range(1, isqrt(limit) + 1):
        square = root**2
        for n in range(square+1, limit+1):
            counts[n] += sf[n-square]
    frequency = Counter(counts[1:])
    assert [n for n in range(1, limit+1) if counts[n] == 0] == [1, 13]
    assert [n for n in range(1, limit+1) if counts[n] == 1] == [
        2, 3, 4, 5, 8, 9, 25, 29, 61
    ]
    assert [counts.index(k, 1) for k in range(1, 26)] == [
        2, 6, 11, 23, 30, 38, 62, 71, 83, 110, 138, 155, 182,
        203, 227, 263, 302, 327, 383, 435, 447, 503, 542, 602, 635
    ]
    assert [frequency[k] for k in range(11)] == [
        2, 9, 19, 27, 38, 36, 57, 63, 62, 74, 94
    ]
    eligible = [n for n in range(1, limit+1) if counts[n] >= 2]
    assert all(m == i + 11 for i, m in enumerate(eligible, 1) if i > 50)
    print(f"All 25 first occurrences and 11 displayed frequencies agree on "
          f"the tested segment 1..{limit:,}. A085267's index formula agrees "
          f"at {len(eligible)-50:,} consecutive finite indices.")


if __name__ == "__main__":
    test_rational_bounds()
    test_conjecture_data()

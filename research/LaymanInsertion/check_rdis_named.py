"""Verify the rational invariant ranges and test the simultaneous insertion rule."""

from fractions import Fraction
from math import isqrt


CASES = [
    ("A082630", Fraction(7, 11), 2, 3, -2, [1, 2, 5, 8]),
    ("A085376", Fraction("0.36704"), 3, 4, -3, [1, 3, 11, 30]),
    ("A080874", Fraction("0.376"), 3, 3, 5, [1, 3, 8, 29]),
    ("A080874", Fraction("0.37802"), 3, 3, 5, [1, 3, 8, 29]),
    ("A085348", Fraction("0.264"), 4, 5, -4, [1, 4, 19, 72]),
    ("A085349", Fraction("0.26688"), 4, 4, 11, [1, 4, 15, 71]),
]


def stable_terms(k, count):
    # Truncating on the right cannot change the first count terms in any
    # later round because no term is removed and each insertion is local.
    values = [1, 1]
    for _ in range(count * (2 + k.denominator // k.numerator)):
        if len(values) >= count and all(
            x * k.denominator < k.numerator * y
            for x, y in zip(values[:count - 1], values[1:count])
        ):
            return values[:count]
        next_values = [values[0]]
        for x, y in zip(values, values[1:]):
            if x * k.denominator >= k.numerator * y:
                next_values.append(x + y)
            next_values.append(y)
            if len(next_values) >= count:
                break
        values = next_values[:count]
    raise AssertionError("The chosen round budget did not reach the stable prefix")


def verify(name, k, q, first_digit, det, initial):
    c = q - 1 / k
    assert 0 < c < 1
    s = Fraction(1, q)

    def polynomial(z):
        return (q + 1) * z * (q - z) - q

    if first_digit == q + 1:
        assert c <= s and polynomial(c) > 0
    else:
        assert s < c and polynomial(q * c / (q + 1)) <= 0

    terms = stable_terms(k, 160)
    assert terms[:4] == initial
    trace = q * (q + 1) - 2
    for i in range(len(terms) - 2):
        digit = first_digit if i % 2 == 0 else 2 * q + 1 - first_digit
        assert terms[i + 2] == digit * terms[i + 1] - terms[i]
    for i in range(len(terms) - 3):
        assert terms[i] * terms[i + 3] - terms[i + 1] * terms[i + 2] == det
    for i in range(len(terms) - 4):
        assert terms[i + 4] == trace * terms[i + 2] - terms[i]
    if name == "A085376":
        pell = []
        cutoff = 100000
        for x in range(1, cutoff + 1):
            square3 = 8 * x * x - 5
            y = isqrt(square3 // 3)
            if 3 * y * y == square3 and y % 2:
                pell.append(x)
        differences = [value - prev for value, prev in zip(terms, [0] + terms)]
        assert [d for d in differences if d <= cutoff] == pell
    print(name, k, "passed both range and 160 stable-term checks")


if __name__ == "__main__":
    for case in CASES:
        verify(*case)


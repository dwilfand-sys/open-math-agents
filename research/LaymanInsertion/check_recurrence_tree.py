"""Check Layman's recurrence-tree coefficient from determinant-one products."""

from fractions import Fraction


def trace_for(base, low, high):
    a, b, c, d = 1, 0, 0, 1
    for j in range(high):
        digit = base + (j + 1) * low // high - j * low // high
        a, b, c, d = digit * a - c, digit * b - d, a, b
    assert a * d - b * c == 1
    return a + d


def check():
    checks = 0
    limit = 40
    for base in range(2, 8):
        def descend(left, right, third_trace):
            nonlocal checks
            a, b = left.numerator, left.denominator
            c, d = right.numerator, right.denominator
            if b + d > limit:
                return
            assert b * c - a * d == 1
            middle = Fraction(a + c, b + d)
            lt, rt = trace_for(base, a, b), trace_for(base, c, d)
            assert trace_for(base, a + c, b + d) == lt * rt - third_trace
            checks += 1
            descend(left, middle, rt)
            descend(middle, right, lt)
        descend(Fraction(0), Fraction(1), 2)
    print(f"Verified {checks} Farey tree nodes through denominator {limit}.")

    initial_pairs = []
    for ratio in [Fraction(1, 2), Fraction(3, 5)]:
        terms = [0, 1]
        for _ in range(100):
            p, q = terms[-2:]
            step = 1 / ratio + Fraction(p, q)
            digit = 1 + step.numerator // step.denominator
            terms.append(digit * q - p)
        assert all(terms[j+4] == 7*terms[j+2] - terms[j] for j in range(1, 97))
        initial_pairs.append(terms[1:3])
    assert initial_pairs == [[1, 3], [1, 2]]
    print("The two (7,2) examples disagree at their second term.")


if __name__ == "__main__":
    check()

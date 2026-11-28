"""Check the row indexing, both valuation contributions, and the sharp row five."""

from functools import cache

from check_a132305_tower import direct_coefficient, valuation


@cache
def row(n):
    values = [1]
    for _ in range(n):
        extended = [0] * (len(values) + 2)
        for i, value in enumerate(values):
            for shift in (0, 1, 2):
                extended[i + shift] += value
        values = extended
    assert len(values) == 2 * n + 1
    assert values == [direct_coefficient(n, j) for j in range(2 * n + 1)]
    return values


def power_sum(n, h, modulus):
    return sum(pow(x, h, modulus) for x in row(n)) % modulus


def check():
    pairs = congruences = sharp = 0
    distinct_pairs = set()
    distinct_congruences = set()
    for p in (5, 7, 11):
        for n, k in ((1, 1), (2, 1), (p, 1), (2*p, 1), (1, 2), (p, 2)):
            top = n * p**k
            if top > 400:
                continue
            low = n * p**(k - 1)
            assert top == p * low
            pairs += 1
            distinct_pairs.add((low, top))
            for h in sorted({2, 3, 5, p, 2*p, p*p, 3*p*p, p**3, p**4}):
                digits = 2 * (k + valuation(n, p)) + valuation(h, p)
                modulus = p**digits
                assert power_sum(top, h, modulus) == power_sum(low, h, modulus)
                congruences += 1
                distinct_congruences.add((low, top, h, modulus))
    for h in sorted(set(range(2, 101)) | {5**b for b in range(1, 10)}):
        b = valuation(h, 5)
        power = 5**(2+b)
        residue = (power_sum(5, h, 5*power) - 3) % (5*power)
        assert residue % power == 0
        digit = residue // power
        expected = 3 if h == 2 else 2 * (h // 5**b) % 5
        assert digit == expected and digit != 0
        sharp += 1
    print(f"{len(distinct_pairs)} distinct row pairs ({pairs} parameter choices), "
          f"{len(distinct_congruences)} distinct congruences ({congruences} parameter choices), "
          f"{sharp} sharp row-five checks")


if __name__ == "__main__":
    check()

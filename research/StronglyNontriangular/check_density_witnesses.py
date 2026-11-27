"""Compare the witness construction with independent exhaustive triangle counts."""

from math import gcd, isqrt


OEIS_PREFIX = [
    2, 4, 7, 13, 22, 25, 31, 52, 61, 73, 82, 88, 97, 115, 133, 145,
    157, 172, 178, 193, 232, 238, 277, 283, 292, 313, 337, 358, 361,
    397, 418, 421, 442, 451, 472, 481, 535, 553, 613, 658, 661, 682,
    718, 733, 742, 757, 802, 817, 841, 871, 922, 955, 973, 997, 1018,
    1048, 1102, 1117, 1123,
]


def prime_sieve(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            prime[p * p::p] = bytes((limit - p * p) // p + 1)
    return prime


def check(limit=100_000):
    prime = prime_sieve(limit + 1)
    counts = [0] * (limit + 1)
    expected = [0] * (limit + 1)
    observed = [0] * (limit + 1)
    for small in range(2, isqrt(2 * limit) + 1):
        # 2P(small,large) >= (small+1)*large, as gcd <= small.
        for large in range(small, 2 * limit // (small + 1) + 1):
            g = gcd(small, large)
            n = (small * large + small + large - g) // 2
            if n <= limit:
                counts[n] += 1
                if g == 1:
                    if small % 2 == 0 and large % 2 == 1 and prime[small+1]:
                        expected[n] += 1
                    if large % 2 == 0 and small % 2 == 1 and prime[large+1]:
                        expected[n] += 1
    assert [n for n in range(2, OEIS_PREFIX[-1]+1) if counts[n] == 0] == OEIS_PREFIX

    candidates = 0
    for q in range(3, limit + 2, 2):
        if prime[q]:
            for n in range(2*q-1, limit+1, q):
                candidates += 1
                a, b = q-1, 2*((n+1)//q)-1
                assert gcd(a, b) == gcd(q-1, 2*n+1)
                if gcd(q-1, 2*n+1) == 1:
                    assert (a*b + a + b - 1) == 2*n
                    observed[n] += 1
    assert observed == expected
    print(f"All {len(OEIS_PREFIX)} published prefix terms through {OEIS_PREFIX[-1]} agree.")
    print(f"Through {limit:,}: {candidates:,} candidate prime divisors, "
          f"{sum(observed):,} coprime witnesses, all checked independently.")
    print(f"Witnesses cover {sum(v > 0 for v in observed):,} positive integers.")
    print(f"{sum(n > 1 and counts[n] == 0 for n in range(limit+1)):,} "
          "integers are strongly nontriangular in this segment.")


if __name__ == "__main__":
    check()

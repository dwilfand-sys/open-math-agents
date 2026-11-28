"""Verify the ten A085264 Lean profile rows using only integer inequalities."""

from math import prod


PRIMES = (3, 5, 7, 11, 13, 17)
SCALE = 2606204601000000
ROWS = [
    (1600, 2047, 2950, 199283), (2048, 4095, 2780, 200323),
    (4096, 8191, 2700, 205000), (8192, 16383, 2889, 205000),
    (16384, 32767, 2874, 205000), (32768, 65535, 2771, 205000),
    (65536, 131071, 2636, 205000), (131072, 262143, 2495, 205000),
    (262144, 524287, 2359, 205000), (524288, 1000000, 2233, 205000),
]


def main():
    counts, premature, best = [], [], None
    for low, high, alpha, reciprocal in ROWS:
        count = 0
        for mask in range(64):
            selected = [p for i, p in enumerate(PRIMES) if mask >> i & 1]
            denominator = prod(selected)
            assert SCALE % denominator == 0
            assert all(SCALE % (p*p) == 0 for p in selected)
            rho = (SCALE // denominator) * prod(p-1 for p in selected)
            refund = sum(SCALE // (p*p) for p in selected)
            cost = alpha*(SCALE//10000) + 2*(reciprocal*(SCALE//1000000) - refund)
            for t in range(5):
                required = denominator * 19**t
                first = max(low, (required-1)//2)
                if required > 2*high+2:
                    assert first > high
                    continue
                assert required <= 2*first+2 and first <= high
                assert first == low or required > 2*(first-1)+2
                slope = rho*18**t - cost*19**t
                degree = len(selected)+t
                denominator_here = SCALE * 19**t
                intercept = (100 + (2**(degree-1) if degree else 0) -
                             len(selected)) * denominator_here
                numerator = first*slope-intercept
                assert slope > 0 and numerator > 0
                if low*slope <= intercept:
                    premature.append((low, first, selected, t))
                if best is None or numerator*best[1] < best[0]*denominator_here:
                    best = numerator, denominator_here, first, selected, t
                count += 1
        counts.append(count)
    assert SCALE % 1000000 == 0
    assert counts == [79, 96, 106, 122, 137, 154, 168, 183, 198, 214]
    numerator, denominator, first, primes, rank = best
    assert numerator*3705625 == 23899061*denominator
    assert (first, primes, rank) == (1600, [5, 7, 11], 0)
    assert len(premature) == 2
    print(f"{sum(counts)} admissible profiles. Minimum margin 23899061/3705625.")
    print("Two profiles would fail the premature band-start comparison:", premature)


if __name__ == "__main__":
    main()

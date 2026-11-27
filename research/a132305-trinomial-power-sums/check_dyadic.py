"""Independent checks of the exact dyadic valuation and normalized quadratic term."""


def row_at_steps(requests, modulus):
    coeff = [1]
    rows = {}
    for n in range(max(requests) + 1):
        if n in requests:
            rows[n] = coeff.copy()
        prev = [0, 0] + coeff + [0, 0]
        coeff = [(prev[i] + prev[i+1] + prev[i+2]) % modulus
                 for i in range(len(coeff) + 2)]
    return rows


def two_order(n):
    assert n != 0
    return (n & -n).bit_length() - 1


def quadratic_coeffs(limit):
    # [x^(2j)] S(x)^2, computed directly with denominators inverted modulo four.
    s = [((1 - 3*(i % 3 == 0))*pow(i, -1, 4)) % 4 if i % 2 else 0
         for i in range(2*limit + 1)]
    return [sum(s[i]*s[2*j-i] for i in range(1, 2*j, 2)) % 4
            for j in range(limit+1)]


def check():
    cases = [(odd << alpha, alpha) for alpha in range(2, 9)
             for odd in range(1, 18, 2) if (odd << alpha) <= 2304]
    exponents = tuple(range(3, 19)) + (24, 31, 32)
    modulus = 2**(2*8 + 6 + 2)
    requests = {r for n, _ in cases for r in (n, n//2)}
    rows = row_at_steps(requests, modulus)
    count = 0
    for n, alpha in cases:
        for h in exponents:
            delta = (sum(pow(a, h, modulus) for a in rows[n]) -
                     sum(pow(a, h, modulus) for a in rows[n//2])) % modulus
            assert two_order(delta) == 2*alpha + two_order(h), (n, h, delta)
            count += 1
    max_m = 100
    small = row_at_steps(set(range(1, 2*max_m + 1)), 4)
    quad = quadratic_coeffs(4*max_m)
    for r in range(2*max_m+1):
        assert quad[2*r] == (2 if r > 0 and r % 2 == 0 and r % 3 else 0)
    for m in range(1, max_m+1):
        u = small[2*m]
        d = [sum(u[i]*quad[j-i] for i in range(j+1)) % 4 for j in range(len(u))]
        for power in (3, 4, 5, 6, 9):
            assert sum(v**(power-1)*w for v, w in zip(u, d)) % 4 == 2
        f = small[m]
        assert sum(f[m-i] for i in range(1, m+1) if i%3) % 2 == 1
    print(f"{count} exact valuations matched for {len(cases)} even rows, "
          f"including alpha=8 and exponent 32.")
    print(f"Direct mod-4 logarithm calculation checked the residual for "
          f"m=1..{max_m} and five exponents.")


if __name__ == "__main__":
    check()

"""Check the ternary extension directly from trinomial rows."""


def v3(n):
    assert n > 0
    order = 0
    while n % 3 == 0:
        order += 1
        n //= 3
    return order


def requested_rows(indices, modulus):
    row = [1]
    saved = {}
    for n in range(max(indices) + 1):
        if n in indices:
            saved[n] = row.copy()
        if n < max(indices):
            pad = [0, 0] + row + [0, 0]
            row = [(pad[i] + pad[i + 1] + pad[i + 2]) % modulus
                   for i in range(len(row) + 2)]
    return saved


def check():
    bases = (1, 2, 4, 5, 7, 8, 10, 11, 13)
    exponents = (3, 4, 5, 6, 7, 8, 9, 10, 12, 17, 18, 27)
    cases = [(base * 3**alpha, alpha) for base in bases for alpha in range(1, 8)
             if base * 3**alpha <= 2200]
    modulus = 3**(2 * max(alpha for _, alpha in cases) + 5)
    indices = {j for n, _ in cases for j in (n, n//3)}
    rows = requested_rows(indices, modulus)
    moments = 0
    coefficients = 0
    for n, alpha in cases:
        large, small = rows[n], rows[n//3]
        for h in exponents:
            b = v3(h)
            strong = 3**(2 * alpha + b)
            required = strong if alpha >= 3 else strong//3
            for j, value in enumerate(large):
                previous = pow(small[j//3], h, strong) if j % 3 == 0 else 0
                d = pow(value, h, strong) - previous
                assert d % (required if j % 3 == 0 else strong) == 0, (n, h, j)
                coefficients += 1
            delta = (sum(pow(a, h, modulus) for a in large)
                     - sum(pow(a, h, modulus) for a in small)) % modulus
            assert delta % required == 0, (n, h, delta)
            if n in (3, 9) and h == 5:
                expected = 1 if n == 3 else 3
                assert v3(delta) == expected
            moments += 1
    # Check the key cancellation by a direct product, without the rational form.
    for s in range(101):
        degree = 9 * s
        coefficient = sum(pow(i*(degree-i), -1, 3) for i in range(1, degree)
                          if i % 3 and (degree-i) % 3)
        assert coefficient % 3 == 0
    print(f"{moments} moments and {coefficients:,} individual powered coefficients "
          f"verified for {len(cases)} row pairs through level seven and exponent 27.")
    print("Both low-level fifth-power obstructions and 101 coefficients "
          "of the squared logarithmic series verified.")


if __name__ == "__main__":
    check()

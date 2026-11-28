"""Exact finite checks of the coefficient lemma and fixed-power supercongruences."""

from math import comb


def multiply(left, right, modulus):
    """Kronecker multiplication with a carry-free, explicitly bounded radix."""
    bound = min(len(left), len(right)) * (modulus - 1) ** 2
    width = max(1, (bound.bit_length() + 7) // 8)
    a = int.from_bytes(b"".join(c.to_bytes(width, "little") for c in left), "little")
    b = int.from_bytes(b"".join(c.to_bytes(width, "little") for c in right), "little")
    length = len(left) + len(right) - 1
    digits = (a * b).to_bytes(width * length, "little")
    return [int.from_bytes(digits[i:i + width], "little") % modulus
            for i in range(0, len(digits), width)]


def polynomial_row(n, modulus):
    result, power = [1], [1, 1, 1]
    while n:
        if n % 2:
            result = multiply(result, power, modulus)
        n //= 2
        if n:
            power = multiply(power, power, modulus)
    return result


def direct_coefficient(n, j):
    """Count words with i twos, j-2i ones, and n-j+i zeros."""
    j = min(j, 2*n-j)
    return sum(comb(n, i) * comb(n-i, j-2*i)
               for i in range(max(0, j-n), j//2 + 1))


def valuation(value, p):
    assert value > 0
    result = 0
    while value % p == 0:
        value //= p
        result += 1
    return result


def check():
    pairs = cells = moments = independent_cells = 0
    powers = (2, 3, 4, 5, 7, 10)
    for p in (5, 7, 11, 13, 17, 19):
        for k in range(1, 6):
            for n in (1, 2, 3, p):
                top = n * p**k
                if top > 6500:
                    continue
                alpha = valuation(top, p)
                modulus = p**(2*alpha + max(valuation(h, p) for h in powers))
                upper = polynomial_row(top, modulus)
                lower = polynomial_row(top//p, modulus)
                for j, c in enumerate(upper):
                    if j % p:
                        assert c % p**alpha == 0
                    else:
                        assert (c-lower[j//p]) % p**(2*alpha) == 0
                for exponent in powers:
                    mod = p**(2*alpha + valuation(exponent, p))
                    up = sum(pow(c, exponent, mod) for c in upper)
                    down = sum(pow(c, exponent, mod) for c in lower)
                    assert (up-down) % mod == 0
                    moments += 1
                for size, row in [(top, upper), (top//p, lower)]:
                    indices = range(len(row)) if size <= 80 else range(22)
                    for j in indices:
                        assert row[j] == direct_coefficient(size, j) % modulus
                        independent_cells += 1
                pairs += 1
                cells += len(upper)
    fifth = sum(direct_coefficient(5, j)**5 for j in range(11))
    assert valuation(fifth-3, 5) == 3
    print(f"{pairs} row comparisons; {cells:,} coefficient checks; "
          f"{moments} power-sum congruences.")
    print(f"{independent_cells:,} entries also matched direct multinomial counting.")
    print(f"A_5(5) = {fifth}; A_5(1) = 3; v_5(difference) = 3.")


if __name__ == "__main__":
    check()

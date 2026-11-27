"""Exact checks for the aligned and unaligned proofs for Hanna's A181069."""

from math import comb


def row(n):
    values = [1]
    for j in range(n):
        values.append(values[-1] * (n - j) // (j + 1))
    return values


def valuation(n, p):
    assert n > 0
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def check_level(p, n):
    r = valuation(n, p)
    assert r > 0
    q = p**r
    modulus = q**3
    m = n // p
    high, high_prev = row(n), row(n - 1)
    low, low_prev = row(m), row(m - 1)
    a_n = sum((pow(v, 3, modulus) * b) % modulus for b, v in zip(high, high_prev))
    a_m = sum((pow(v, 3, modulus) * b) % modulus for b, v in zip(low, low_prev))
    assert (a_n - a_m) % modulus == 0

    def reflected(b, u, v):
        return (b * b * (b * b - 3 * u * v)) % modulus

    prefix = weighted = abel_interior = unaligned = aligned_residue = reflected_sum = 0
    for j in range(1, n + 1):
        inverse_square = pow(j, -2, q) if j % p else 0
        prefix = (prefix + inverse_square) % q
        s = min(valuation(j, p), r)
        assert prefix % (p**s) == 0
        weight = pow(high_prev[j - 1], 4, q)
        weighted = (weighted + weight * inverse_square) % q
        if j == n:
            assert (weight * prefix - abel_interior - weighted) % q == 0
            break
        difference = pow(high_prev[j], 4, q) - weight
        assert difference % (p ** (r - s)) == 0
        assert difference * prefix % q == 0
        abel_interior = (abel_interior + difference * prefix) % q
        term = reflected(high[j], high_prev[j - 1], high_prev[j])
        reflected_sum += term
        if j % p == 0:
            k = j // p
            lower_term = reflected(low[k], low_prev[k - 1], low_prev[k])
            assert (term - lower_term) % modulus == 0
            divisor = p ** (r + 2 * s + valuation(low[k], p))
            assert (high[j] - low[k]) % divisor == 0
            aligned_residue += term - lower_term
        else:
            assert (term - 3 * n * n * weight * pow(j, -2, q)) % modulus == 0
            unaligned += term
    assert (2 + reflected_sum - 2 * a_n) % modulus == 0
    assert weighted == unaligned % modulus == aligned_residue % modulus == 0
    return n, sum(j % p == 0 for j in range(1, n))


def main():
    cases = {(p, n * p**r) for p in (5, 7, 11, 13, 17, 19, 23)
             for r in (1, 2, 3, 4) for n in (1, 2, 3, p)
             if n * p**r <= 3500}
    count = aligned = 0
    for p, n in sorted(cases):
        rows, aligned_here = check_level(p, n)
        count += rows
        aligned += aligned_here
    exact_high = sum(comb(6, j)**3 * comb(7, j) for j in range(7))
    assert (exact_high - 1) % 343 == 0 and (exact_high - 1) % 2401 != 0
    print(f"{len(cases)} distinct towers, {count} prefix and weight checks, "
          f"{aligned} aligned ratio transfers. "
          f"The first 7-adic difference is {exact_high - 1} with valuation exactly three.")


if __name__ == "__main__":
    main()

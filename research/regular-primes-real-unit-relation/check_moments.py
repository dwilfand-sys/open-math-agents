"""Independently test RegularPrimes.R2.H2.R1.H2 in F_p[T]/(T^(p-1)).

The polynomial relation uses a=0,...,(p-3)/2-1, length b=a+2 geometric
factors and exponents 2*e[a]. Logarithmic derivatives recover all exponent
vectors satisfying the relation. Each reported vector is then verified by
direct polynomial powering. Rational Bernoulli numbers are computed separately
from their binomial recurrence. Run with Python 3.10 or later.
"""

from fractions import Fraction
from itertools import product
from math import comb, prod


def multiply(f, g, p):
    order = len(f)
    answer = [0] * order
    for i, a in enumerate(f):
        if a:
            for j in range(order-i):
                answer[i+j] += a*g[j]
    return [a % p for a in answer]


def power(f, exponent, p):
    answer = [1] + [0]*(len(f)-1)
    while exponent:
        if exponent % 2:
            answer = multiply(answer, f, p)
        exponent //= 2
        if exponent:
            f = multiply(f, f, p)
    return answer


def geometric(length, p):
    """Sum the shifted monomials as polynomials, retaining degrees 0..p-2."""
    return [sum(comb(i, k) for i in range(k, length)) % p for k in range(p-1)]


def logarithmic_derivative(f, p):
    """Coefficients of f'/f by power-series division, through degree p-3."""
    result = []
    inv = pow(f[0], -1, p)
    for k in range(len(f)-1):
        correction = sum(f[k-j] * result[j] for j in range(k))
        result.append(((k+1)*f[k+1] - correction) * inv % p)
    return result


def kernel_basis(columns, p):
    matrix = [list(row) for row in zip(*columns)]
    rank = 0
    pivots = []
    for j in range(len(columns)):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][j]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][j], -1, p)
        matrix[rank] = [inverse*t % p for t in matrix[rank]]
        for i, row in enumerate(matrix):
            if i != rank and row[j]:
                matrix[i] = [(a-row[j]*b) % p for a, b in zip(row, matrix[rank])]
        pivots.append(j)
        rank += 1
    basis = []
    for free in sorted(set(range(len(columns))) - set(pivots)):
        vector = [0]*len(columns)
        vector[free] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -matrix[i][free] % p
        basis.append(vector)
    return basis


def bernoulli_numbers(through):
    """Use sum binom(n+1,k)*B_k = 0 for n≥1, with B_0=1."""
    values = [Fraction(1)]
    for n in range(1, through+1):
        earlier = sum(comb(n+1, k)*b for k, b in enumerate(values))
        values.append(-earlier/(n+1))
    return values


def polynomial_relation(p, factors, lengths, e, shift):
    """Test the original congruence, including its constant coefficient c."""
    one = [1] + [0]*(p-2)
    shifted = [1, 1] + [0]*(p-3)
    result = one
    for f, exponent in zip(factors, e):
        if exponent:
            result = multiply(result, power(f, 2*exponent, p), p)
    c = prod(pow(b, 2*x, p) for b, x in zip(lengths, e)) % p
    expected = [c*v % p for v in power(shifted, shift, p)]
    assert c != 0 and c == result[0]
    return result == expected, c


def weighted_moments(p, lengths, e, bernoulli):
    return {
        k: (raw, bernoulli[k].numerator * raw % p)
        for k in range(2, p-1, 2)
        for raw in [sum(x*(pow(b, k, p)-1) for b, x in zip(lengths, e)) % p]
    }


def inverse_series(f, p):
    inverse_constant = pow(f[0], -1, p)
    result = [inverse_constant]
    for k in range(1, len(f)):
        result.append(-inverse_constant * sum(f[k-j]*result[j] for j in range(k)) % p)
    return result


def check_real_unit_transport(p, lengths, factors, e, shift, c):
    """Exercise the pth-power relation and the reversal used to clear ξ⁻¹."""
    one = [1] + [0]*(p-2)
    xi = [1, 1] + [0]*(p-3)
    xi_inverse = inverse_series(xi, p)
    real_generators = []
    for b, forward in zip(lengths, factors):
        backward = [0]*(p-1)
        term = one
        for _ in range(b):
            backward = [(x+y) % p for x, y in zip(backward, term)]
            term = multiply(term, xi_inverse, p)
        assert backward == multiply(power(xi_inverse, b-1, p), forward, p)
        real_generators.append(multiply(forward, backward, p))

    def generator_product(exponents):
        value = one
        for g, f in zip(real_generators, exponents):
            base = inverse_series(g, p) if f < 0 else g
            value = multiply(value, power(base, abs(f), p), p)
        return value

    actual_constant = [c] + [0]*(p-2)
    assert generator_product(e) == actual_constant
    cleared_shift = sum(x*(b-1) for x, b in zip(e, lengths))
    assert cleared_shift % p == shift
    assert polynomial_relation(p, factors, lengths, e, cleared_shift) == (True, c)
    # Start from signed exponents f=e+p*h and a nonconstant local unit w.
    # Both the input relation and its normalization are tested by ring arithmetic.
    w = [c, 3, 1] + [0]*(p-4)
    assert power(w, p, p) == actual_constant
    h = [(j % 5)-2 for j in range(len(e))]
    f = [ex+p*q for ex, q in zip(e, h)]
    v = generator_product(h)
    minus_v = [(-a) % p for a in v]
    u = multiply(w, minus_v, p)
    assert power(u, p, p) == [(-a) % p for a in generator_product(f)]
    assert multiply(u, inverse_series(minus_v, p), p) == w
    assert [ex % p for ex in f] == e


def check_prime(p, irregular_indices, bernoulli):
    lengths = list(range(2, (p-1)//2+1))
    factors = [geometric(b, p) for b in lengths]
    columns = [[2*t % p for t in logarithmic_derivative(f, p)] for f in factors]
    # The last unknown s has coefficient -1/(1+T), independently of e.
    # The difference of logarithmic derivatives vanishes exactly when the
    # quotient is constant: all positive degrees 1,...,p-2 are units mod p.
    columns.append([(-1 if k % 2 == 0 else 1) % p for k in range(p-2)])
    basis = kernel_basis(columns, p)
    exact_indices = [k for k in range(2, p-1, 2) if bernoulli[k].numerator % p == 0]
    assert exact_indices == irregular_indices
    assert len(basis) == len(irregular_indices)
    zero = [0]*len(factors)
    assert polynomial_relation(p, factors, lengths, zero, p) == (True, 1)
    assert all(raw == weighted == 0 for raw, weighted in weighted_moments(p, lengths, zero, bernoulli).values())
    if p <= 7:
        direct_count = 0
        for e in product(range(p), repeat=len(lengths)):
            shift = sum(x*(b-1) for x, b in zip(e, lengths)) % p
            direct_count += polynomial_relation(p, factors, lengths, e, shift)[0]
        assert direct_count == p**len(basis)
    for vector in basis:
        e, shift = vector[:-1], vector[-1]
        assert any(e)
        raw = weighted_moments(p, lengths, e, bernoulli)
        assert [k for k, (value, _) in raw.items() if value] == irregular_indices
        assert all(weighted == 0 for _, weighted in raw.values())
        passed, constant = polynomial_relation(p, factors, lengths, e, shift)
        assert passed
        check_real_unit_transport(p, lengths, factors, e, shift, constant)
        # Exhaust the nonzero vectors on this one-dimensional line, verifying
        # the hypotheses and conclusion directly for every scalar.
        assert len(basis) == 1
        for scalar in range(2, p):
            scaled = [scalar*x % p for x in e]
            assert polynomial_relation(p, factors, lengths, scaled, scalar*shift % p)[0]
            assert all(weighted == 0 for _, weighted in weighted_moments(p, lengths, scaled, bernoulli).values())
        print(f"p={p} nonzero basis e={e}, shift={shift}, c={constant}")
        print("  nonzero unweighted moments", {k: raw[k][0] for k in irregular_indices})

    # These vectors have the correct constant and linear terms, but fail the
    # full polynomial hypothesis and the conclusion. They are negative controls.
    for j, length in enumerate(lengths):
        e = zero.copy()
        e[j] = 1
        assert not polynomial_relation(p, factors, lengths, e, length-1)[0]
        assert any(weighted for _, weighted in weighted_moments(p, lengths, e, bernoulli).values())
    print(f"p={p}: kernel dimension {len(basis)}, {p**len(basis)} satisfying vectors, "
          f"{len(lengths)} rejected unit-vector controls")


def main():
    cases = {3: [], 5: [], 7: [], 11: [], 13: [], 17: [], 19: [], 23: [], 29: [],
             31: [], 37: [32], 41: [], 43: [], 47: [], 53: [], 59: [44], 61: [], 67: [58]}
    bernoulli = bernoulli_numbers(max(cases)-3)
    assert bernoulli[1] == Fraction(-1, 2) and bernoulli[12] == Fraction(-691, 2730)
    for p, irregular in cases.items():
        check_prime(p, irregular, bernoulli)


if __name__ == "__main__":
    main()

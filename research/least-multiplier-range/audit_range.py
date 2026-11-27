"""Symbolic, independent verification of the three inequalities in the attainment proof."""
import sympy as sp

k, m, d, p = sp.symbols("k m d p", integer=True)
a = 2 * k / (2 * k - 1)
b = 2 * (k - 1) / (2 * k - 3)

# The gap between consecutive extrema is strictly positive for k >= 2.
assert sp.simplify((b - a) * (2 * k - 1) * (2 * k - 3)) == 2

# The explicit prime cutoff for passing from a product below a to one still below b.
assert sp.simplify(a / (b - a) - k * (2 * k - 3)) == 0
step_margin = (b - a * (1 + 1 / p)) * p * (2 * k - 1) * (2 * k - 3)
assert sp.simplify(step_margin - 2 * (p - k * (2 * k - 3))) == 0

# For deficient m < k, write sigma(m) = 2m - d with integer d >= 1.
# Both terms in this decomposition of the required margin are nonnegative.
margin = (2 * k - 3) * m - (k - 1) * (2 * m - d)
assert sp.expand(margin - ((k - 1) * (d - 1) + k - 1 - m)) == 0
print("Verified the interval width, the exact large-prime cutoff, the one-prime"
      " overshoot margin, and the deficit bound for every smaller multiplier.")

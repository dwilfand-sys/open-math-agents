# Even almost-perfect numbers with few odd prime factors

An even integer has a unique expression `2^k * u` with `k > 0` and `u` odd. An integer is almost perfect when its divisor sum is one less than twice the integer. The theorem `OMA.AlmostPerfectTwoOdd.odd_core_one_or_three` in [TwoOddPowers.lean](TwoOddPowers.lean) states that an even almost-perfect integer has `u = 1` or at least three distinct prime divisors of `u`.

The two-prime exclusion draws on Ibrahim Amin Nicola Shnoudi's argument for odd quasiperfect numbers at general levels. After setting `q = 2^(k+1) − 1`, the almost-perfect equation gives a geometric-sum equation in two odd prime powers. Parity forces both exponents to be even. After clearing denominators, size bounds leave the case where both exponents are two. A quadratic identity then requires a square equal to `3q + 1`. This integer is two modulo four. [Shnoudi's account](https://lifeofresearch.com/articles/144)

The range of arbitrary positive exponents, the single-prime case, and the reduction from the prime factorization are all included in the Lean source. This checkpoint is based on the A215926 parent reduction by @Hiphex. [Upstream PR #4232](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4232)

## Verification

Run `python check_two_odd.py` with Python 3 and SymPy. The checker expands both polynomial identities independently, checks 225,000 geometric-sum inequalities, and calculates divisor sums by a sieve through 500,000. The sieve covers 18 even powers of two, 47,985 even integers with one distinct odd prime divisor, and 110,140 with two. These counts include all positive exponents. The inequalities in the Lean source were also reviewed individually. Compilation with the project's pinned Lean kernel remains pending.

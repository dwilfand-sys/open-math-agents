# Which least deficient multipliers occur?

For each integer `n ≥ 2`, OEIS A215926 selects the least deficient `k` for which `kn` is perfect or abundant. The theorem `OMA.AlmostPerfectConverse.range_characterization` in [LeastMultiplierRange.lean](LeastMultiplierRange.lean) identifies every value of this sequence. Its range consists of 3 and all almost-perfect numbers, where almost-perfect means `1 + σ(k) = 2k`. As a consequence, the OEIS prediction that every term is 1, 3 or a power of two is equivalent to the assertion that all almost-perfect numbers are powers of two. Both conjectures remain open.

The inclusion from sequence values to the indicated set adapts the accepted forward reduction by @Hiphex, which credits Naitik Gupta's first-occurrence argument. For even arguments the sequence value is at most 3. For odd arguments the least multiplier is below the smallest prime factor of the argument. If the multiplier has deficiency at least two, the largest power of two below it works as well. Minimality makes these multipliers equal. [Upstream PR #4232](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4232) · [Upstream PR #906](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/906)

For the converse, let `k ≥ 2` be almost perfect. Choose a squarefree product `n` of primes greater than `k` such that

$$
\frac{2k}{2k-1} \;\leq\; \frac{\sigma(n)}{n}
\;<\; \frac{2(k-1)}{2k-3}.
$$

To construct it, multiply factors `1 + 1/p` with primes `p > k(2k − 3)` until the lower endpoint is reached. The sum of reciprocals of a sufficiently long finite set of these primes is at least one half, and their product of `1 + 1/p` is at least one plus that sum. At the first crossing the prime cutoff guarantees the strict upper bound. The lower bound makes `kn` non-deficient. For each deficient `m < k`, its abundancy is at most `2 − 1/(k − 1)`. Since every such `m` is coprime to `n`, the upper bound makes `mn` deficient. Thus the least qualifying multiplier is exactly `k`. The values 1 and 3 occur at 6 and 2 respectively. [Mathlib's finite prime-reciprocal bound](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SumPrimeReciprocals.html)

## Verification

Run `python audit_range.py` with SymPy to verify the interval width, the explicit prime cutoff, the one-prime overshoot inequality, and the bound for a smaller multiplier written in terms of its integer deficiency. Run `python check_converse.py` for a separate direct calculation with exact integer arithmetic. It constructs witnesses to each of the 499 intervals for `2 ≤ k ≤ 500`, checks every smaller deficient multiplier, and directly computes the sequence for arguments through 500 by summing divisors over multiples. The observed range on that finite interval is 1, 2, 3, 4, 8, 16, 32, 64, 128, and 256. Compilation with the project's pinned Lean kernel remains pending.

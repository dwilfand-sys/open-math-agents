# How many choices of a first powerful summand are needed?

Let P be the positive powerful numbers and P₀=P∪{0}. Zero denotes an unused summand. Write V(X) for the number of positive integers up to X that are sums of two members of P. Valentin Blomer proved

**V(X) = X (log X)^(−α+o(1)), where α = 1−2^(−1/3) ≈ 0.206299474.**

This published theorem supplies the estimate below. The deductions are applications of it to the choice of offsets in the Mollin–Walsh problem. [Blomer, Journal of the London Mathematical Society 71 (2005), 69–84](https://doi.org/10.1112/S0024610704006040)

### Arbitrary and growing sets of offsets

For any set C_X of nonnegative integer offsets, count the positive n≤X that can be written as c+u+v with c∈C_X and u,v∈P₀. For fixed c such a number belongs to the translate c+(P₀+P₀). Only offsets c≤X matter, and this translate contains at most V(X)+#(P∩[1,X])+1 eligible integers. The powerful numbers up to X number at most ζ(3/2)√X. Indeed every positive powerful integer has the form a²b³, and summing √X/b^(3/2) over b≥1 is an upper bound. Consequently

**#covered ≤ #C_X · (V(X) + ζ(3/2)√X + 1).**

The estimate is uniform in the offsets. If #C_X≤(log X)^(α−ε) for a fixed ε>0, it gives #covered=o(X), even if C_X is chosen separately at every X. A fixed nonempty finite C therefore covers a set of density zero. Even within any fixed positive-density set of target integers, a proportion tending to one are missed. This applies to the squarefree integers congruent to 7 modulo 8, the subfamily left by the three-square reduction. Its density is 1/π², from (1/8)∏_{p odd}(1−p⁻²).

A useful equivalent bound concerns the sizes of actual summands. For every fixed 0<δ<2α, almost all positive n admit no representation by at most three powerful numbers using a summand from

**{0} ∪ {c∈P : c≤(log n)^(2α−δ)}.**

To check this, take C_X to consist of zero and every powerful c≤(log X)^(2α−δ). Its cardinality is at most 1+ζ(3/2)(log X)^(α−δ/2), so the same calculation applies. Permuting the three summands puts the smallest in the first position. Heath-Brown proved that each sufficiently large positive integer admits some representation by at most three powerful numbers. Together these two theorems show that, for a density-one set of integers, every such representation uses three positive summands, each larger than the stated function of n. [Heath-Brown reference and problem history in OEIS A056828](https://oeis.org/A056828)

### Simultaneous and prime-target limitations

For each sequence of finite offset lists C₁,C₂,…, one can choose a strictly increasing sequence of squarefree n_j≡7 (mod 8) such that n_j avoids c+P₀+P₀ for every c in C₁∪⋯∪C_j. At each stage only a fixed finite union of translates is excluded, so the natural density of eligible squarefree choices remains 1/π². The quantitative estimate above applies directly to lists that grow with X at its specified rate.

In fact, every residue modulo every M≥2 has a representation as a positive square plus a positive powerful number. To see this, let r be the target and put b equal to the product of the primes dividing M that do not divide r (the empty product is 1). For each prime p dividing M, either p divides r and not b, or p divides b and not r. Hence r−b² is coprime to M. Choose a positive unit u congruent to r−b² modulo M. Euler's theorem gives u^(φ(M)+1)≡u modulo M, and this power is powerful because its exponent is at least 2. Therefore r≡b²+u^(φ(M)+1) modulo M. In particular, any proposed finite collection of purely congruential obstructions to two powerful summands fails already modulo the least common multiple of its moduli. This local result gives no bound on the sizes of the summands.

The proof uses density in the integers. It gives no conclusion about the fraction of primes missed, since primes themselves have natural density zero. The separate Chinese-remainder argument for c+x²+y² gives infinitely many prime targets avoiding a fixed finite list of offsets when the other summands are squares. Two arbitrary powerful summands may represent integers having some primes congruent to 3 modulo 4 to odd valuation. The two-square obstruction therefore cannot be transferred to them by imposing those same congruences. Neither observation supplies an exception to the unrestricted Mollin–Walsh conjecture.

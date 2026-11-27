# Infinitely many counterexamples to the prime-root assertions in A301517 and A318807

Let S(n) be the sum of the squarefree positive divisors of n and T(n) the sum of its other positive divisors. For a counterexample to the first assertion we require T(n)/S(n) to be a square with composite positive root. The second assertion additionally requires S(n) and T(n) to be perfect squares.

The original disproofs are due to @anmolspace in [#7662](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7662) and [#9203](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9203). The smaller witnesses in [#10580](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10580) and [#10582](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10582) yield the following family statements. This note gives mathematical proofs. The two submitted Lean files establish the individual numerical counterexamples.

## Squarefree extensions

If u is squarefree and coprime to n, a divisor of nu is uniquely d·e with d dividing n and e dividing u. It is squarefree exactly when d is squarefree. Summing over e shows that S(nu)=σ(u)S(n) and T(nu)=σ(u)T(n), where σ is the usual divisor sum. The ratio is unchanged. If σ(u) is a square, multiplying by u also preserves the property that each sum is a square.

## Positive lower density for the first assertion

Put b=19,773,000=2³·3²·5³·13³. Here S(b)=1,008 and T(b)=72,398,592=268²S(b). Since 268=4·67, every bu with u squarefree and coprime to 390 is a counterexample to the first assertion. This subfamily has natural density
```
(1/b) · ∏_{p|390}(1−1/p) · ∏_{p∤390}(1−1/p²)
= (1/b) · (6/π²) · (65/168)
≈ 1.1895508552 × 10⁻⁸.
```
To justify the density, first exclude the finitely many forbidden congruence classes modulo p for p dividing 390 and modulo p² for primes p≤Y not dividing 390. The Chinese remainder theorem gives the corresponding finite product. Among u≤x the number missed by this sieve because p² divides u for some p>Y is at most x times the sum of 1/j² over integers j>Y. This tends to zero after division by x and passage to Y→∞. The substitution n=bu divides the density by b.

## Infinitely many counterexamples to the second assertion

For each integer cutoff N≥2, there exists a squarefree u>1 whose prime factors all exceed N and for which σ(u) is a perfect square.

To prove this lemma, take a power of two X>N with more than π(N) primes in (X,2X). Such dyadic intervals exist at arbitrarily large X. Otherwise the sum of reciprocals of the primes would converge by comparison with a geometric series, contrary to Euler's theorem. Here π(y) counts primes at most y.

For every prime N<p<2X, encode p+1 by the parities of its prime exponents. All coordinates belong to the π(X) primes at most X because p+1 is even and at most 2X. The number of vectors is π(X)−π(N) plus the number of primes in (X,2X), strictly greater than π(X). A nonempty subset sums to zero over the two-element field. Set u to the product of its distinct primes p. Then σ(u)=∏(p+1) is a square and every prime divisor of u exceeds N. This proves the lemma. Choosing each successive cutoff larger than every earlier prime factor yields infinitely many pairwise coprime multipliers.

Now b′=251b=4,963,023,000 has S(b′)=504² and T(b′)=135,072²=(268·504)². Apply the lemma with N at least 251. Every b′u supplies a counterexample to the second assertion with the same composite root 268. For instance u=7·17 is already coprime to b′ and σ(u)=144. The resulting n=590,599,737,000 has S(n)=6,048² and T(n)=1,620,864². Direct enumeration of its 1,536 positive divisors gives 36,578,304 and 2,627,200,106,496 respectively.

Squarefree integers with perfect-power divisor sums have an established literature. The argument above includes the avoidance of an arbitrary finite set of primes needed for the extension. For context see [Banks, Friedlander, Pomerance and Shparlinski, §6](https://mospace.umsystem.edu/server/api/core/bitstreams/7a236c69-c40e-4c34-89d0-36c025a2560c/content) and the [discussion of squarefree n with σ(n) a power](https://mathoverflow.net/questions/200892/numbers-n-such-that-the-sum-of-the-divisors-of-n-is-a-nontrivial-power).

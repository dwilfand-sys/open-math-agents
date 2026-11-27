# Two counterexamples to Zhi-Wei Sun’s A279821 exhaustion conjecture

Let T(n) be the coefficient of xⁿ in (1+x+x²)ⁿ. In 2016 Zhi-Wei Sun asked whether the eleven listed composite integers n for which n is not the square of a prime and T(n) ≡ 1 modulo n exhaust [A279821](https://oeis.org/A279821). Here are two further members:

| n | Distinct prime factors |
|---:|---|
| 1,316,632,279 | 31 · 42,472,009 |
| 1,793,930,422 | 2 · 37 · 24,242,303 |

Both numbers exceed the largest listed member, 254,677, and are squarefree. Either one disproves the exhaustion conjecture. The [exhaustive census](census/README.md) has verified all terms through 200,000,000. Their positions in the increasing sequence have not yet been determined. Sun’s separate conjecture about congruence modulo n² is a different question.

## Proof

Let P(x)=x⁻¹+1+x, so T(n) is the constant term of P(x)ⁿ. For prime p, integers k≥0 and 0≤d<p, Frobenius gives P(x)^(pk+d) ≡ P(x)ᵈ P(xᵖ)ᵏ modulo p. Every exponent of the latter factor is divisible by p. Among exponents −d,…,d of the former factor the only multiple of p is 0. Thus T(pk+d) ≡ T(k)T(d) modulo p. Iterating gives a product over base-p digits. Deutsch and Sagan proved this exact digit rule in Theorem 4.7 of their 2006 paper. Henningsen and Straub give a broader result. [Deutsch and Sagan, Congruences for Catalan and Motzkin numbers and related sequences](https://doi.org/10.1016/j.jnt.2005.06.005) [Generalized Lucas congruences and linear p-schemes](https://arminstraub.com/downloads/pub/generalized-lucascongruences.pdf)

The digit certificates follow, with the least significant digit first. Small central coefficients can be computed directly as T(d)=Σᵢ C(d,2i)C(2i,i).

| n | p | Digits | T(d) mod p in digit order | Product mod p |
|---:|---:|---|---|---:|
| 1,316,632,279 | 31 | 0,25,19,20,30,14,1 | 1,4,25,1,1,9,1 | 1 |
| 1,316,632,279 | 42,472,009 | 0,31 | 1,1 | 1 |
| 1,793,930,422 | 2 | binary | every factor is 1 | 1 |
| 1,793,930,422 | 37 | 0,28,2,7,32,25 | 1,9,3,23,8,26 | 1 |
| 1,793,930,422 | 24,242,303 | 0,74 | 1,1 | 1 |

The large-prime reductions are exact integer identities:

- T(31)=53,876,592,856,681=1+1,268,520·42,472,009.
- T(74)=11,487,117,228,265,155,906,523,774,113,186,123=1+473,845,955,488,022,565,616,961,974·24,242,303.

Trial division up to the integer square roots 6,517 and 4,923 verifies primality of the two large factors. The Chinese remainder theorem now gives T(n)≡1 modulo n for each displayed n.

A third member, 8,631,398,911,361,689 = 205,129³, follows from the historically known exceptional prime 205,129 and the central-trinomial congruence. The [prime-cube supplement](prime-cube.md) gives the proof, its literature provenance, and the explicit residue modulo the fourth power.

## Modulo the square

The residues of T(n) modulo n² are, respectively, 223,733,948,606,370,725 and 349,250,221,206,625,829. Thus neither example satisfies the stronger prime-characterization congruence. The [separate exact checker](check_prime_squares.py) gives the modulo-p² digit reduction and reconstructs these residues by CRT.

For a prime p≥5 put Hₚ=Σ_{i=1}^{⌊p/3⌋}1/i² modulo p. A further consequence of [Pan and Sun’s central trinomial congruence](https://arxiv.org/abs/2012.05121) is that p³ is a member of A279821 if and only if Hₚ=0. Indeed T(p³)≡T(p) modulo p³ by the adjacent quadratic bound, and (T(p)−1)/p²≡Hₚ/3 modulo p. When Hₚ is nonzero, vₚ(T(pᵃ)−1)=2 for every a≥1, since all adjacent differences from level 2 onward are divisible by p⁴. Therefore no pᵃ, a≥3, then belongs to this sequence.

## Lean research draft

The [single-file Lean draft](A279821.lean) states the complete-list and square-modulus conjectures separately and formalizes the first counterexample. Its source has no proof placeholders and awaits a Lean kernel verdict. No A279821 statement or matching assignment was found on Left to Solve.

## Discovery and verification

These witnesses were found by dwilfand-sys using Codex. To look for n=mq with m squarefree and q a prime greater than m, factor T(m)−1. Every such q dividing that integer automatically gives T(mq)≡1 modulo q. Test the other prime factors of m with the digit formula. Choosing m=31 and m=74 gives the two displayed witnesses. The attached dependency-free verifier recomputes every certificate by trial division and two independent definitions of T(d).

The [current OEIS source](https://github.com/oeis/oeisdata/blob/main/seq/A279/A279821.seq) records the original eleven terms and the exhaustion conjecture. Searches by identifier, conjecture text and exact witness values found no earlier report of these two witnesses. Historical priority remains unestablished. This research note carries no Lean kernel or Left to Solve acceptance claim.

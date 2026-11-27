# Two counterexamples to Zhi-Wei Sun’s A279821 exhaustion conjecture

Let T(n) be the coefficient of xⁿ in (1+x+x²)ⁿ. In 2016 Zhi-Wei Sun asked whether the eleven listed composite integers n for which n is not the square of a prime and T(n) ≡ 1 modulo n exhaust [A279821](https://oeis.org/A279821). Here are two further members:

| n | Distinct prime factors |
|---:|---|
| 1,316,632,279 | 31 · 42,472,009 |
| 1,793,930,422 | 2 · 37 · 24,242,303 |

Both numbers exceed the largest listed member, 254,677, and are squarefree. Either one disproves the exhaustion conjecture. Their positions in the increasing sequence have not been determined. Sun’s separate conjecture about congruence modulo n² is a different question.

## Proof

Let P(x)=x⁻¹+1+x, so T(n) is the constant term of P(x)ⁿ. For prime p, integers k≥0 and 0≤d<p, Frobenius gives P(x)^(pk+d) ≡ P(x)ᵈ P(xᵖ)ᵏ modulo p. Every exponent of the latter factor is divisible by p. Among exponents −d,…,d of the former factor the only multiple of p is 0. Thus T(pk+d) ≡ T(k)T(d) modulo p. Iterating gives a product over base-p digits. This standard central-trinomial Lucas congruence is a special case of the theorem of Henningsen and Straub. [Generalized Lucas congruences and linear p-schemes](https://arminstraub.com/downloads/pub/generalized-lucascongruences.pdf)

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

## Discovery and verification

These witnesses were found by dwilfand-sys using Codex. To look for n=mq with m squarefree and q a prime greater than m, factor T(m)−1. Every such q dividing that integer automatically gives T(mq)≡1 modulo q. Test the other prime factors of m with the digit formula. Choosing m=31 and m=74 gives the two displayed witnesses. The attached dependency-free verifier recomputes every certificate by trial division and two independent definitions of T(d).

The [current OEIS source](https://github.com/oeis/oeisdata/blob/main/seq/A279/A279821.seq) records the original eleven terms and the exhaustion conjecture. Searches by identifier, conjecture text and exact witness values found no earlier report of these two witnesses. Historical priority remains unestablished. This research note carries no Lean kernel or Left to Solve acceptance claim.

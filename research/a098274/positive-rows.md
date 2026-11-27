# A098274 and two cubic supercongruences

Peter Bala recorded the following question on October 5, 2026. Write a(n) for the sum over j = 0,…,n of C(n,j)² C(n+j,j) C(n+2j,2j). For prime p ≥ 5, r ≥ 1 and N = mpʳ with m ≥ 1, both a(N) ≡ a(N/p) and a(N−1) ≡ a(N/p−1) hold modulo p^(3r).

## Prior mathematical results

Both congruences already follow from Matthijs Coster’s Theorem 4 and an identity of Wadim Zudilin. Immediately after Theorem 3 on page 8, Zudilin identifies the positive sum with (−1)ⁿ times the sum of (−1)ʲ C(n,j) C(n+j,j)³. The inner sum is Coster’s W(n,1,3,−1). His ordinary congruence applies with A=1, B=3, e=−1, and his predecessor congruence applies with B≥2. The outer signs agree across each comparison because p is odd. Bala also established the special case a(p−1) ≡ 1 modulo p⁵ for p≥7, as recorded by OEIS.

[Coster, Supercongruences, CWI report AM-R8918, Theorem 4 (1989)](https://ir.cwi.nl/pub/5804/5804D.pdf#page=7) · [Zudilin, Approximations to -, di- and tri- logarithms (2004), p. 8](https://arxiv.org/pdf/math/0409023#page=8) · [OEIS A098274](https://oeis.org/A098274)

## Direct proof for the positive summands

This argument works with the displayed sequence. It uses the Jacobsthal binomial ratio congruence and the full and half inverse-square sums used by Osburn, Sahu and Straub. A finite summation by parts records where the harmonic sums enter. [Osburn, Sahu and Straub, Supercongruences for sporadic sequences, Lemmas 2.1–2.2](https://arxiv.org/abs/1312.2195)

Write M=N/p. Take r=vₚ(N), which only strengthens the required modulus if p divides m. Write T⁺(N,j) for the ordinary summand and T⁻(N,j) for the summand of a(N−1), extended to j=N by zero. Thus T⁻(N,j) = C(N−1,j)² C(N+j−1,j) C(N+2j−1,2j).

### Aligned indices

Suppose p divides j>0 and put s=min(r,vₚ(j)). The scaled-to-unscaled ratios of the three ordinary binomials equal 1 modulo p^(r+2s) in the localization of the integers at p. Apply Jacobsthal to the pairs of parts (j,N−j), (j,N), (2j,N). In these above-scale coordinates, the exponent in the ratio congruence is the sum of the valuations of the parts and their sum. For each pair one of these three numbers is N and the other two have valuation at least s. If a part is zero the ratio is exactly 1.

Replacing C(A,k) by C(A−1,k) introduces the scale-invariant factor (A−k)/A. Thus multiplication by the same three ratios also transports the shifted terms, including the zero case k=A>0. The lower ordinary summand contains C(M,j/p)², divisible by p^(2(r−s)) by binomial absorption. In the lower shifted summand each rising binomial contributes p^(r−s), since C(M+t−1,t) = (M/t) C(M+t−1,t−1), for t=j/p or 2j/p. When s=r these lower bounds follow directly from integrality. Together these estimates give the two aligned comparisons modulo p^(3r). At j=0 both terms are 1. At j=N the shifted comparison is 0=0 and the ordinary comparison uses the two rising ratios.

### Remaining indices

For j>0 define

- W⁺(j) = C(N−1,j−1)² C(N+j,j) C(N+2j,2j).
- W⁻(j) = C(N−1,j)² C(N+j−1,j−1) C(N+2j−1,2j−1).

Binomial absorption gives j² T⁺(N,j)=N² W⁺(j) and 2j² T⁻(N,j)=N² W⁻(j). The successive quotient of R(t)=C(N+t,t) is 1+N/t. For the squared falling binomial the successive quotient is (1−N/t)², with t=j in the plus weight and t=j+1 in the minus weight. The three remaining denominators are j+1,2j+1,2j+2 in the plus weight and j,2j,2j+1 in the minus weight. The consecutive-term formulas apply for 1≤j<N including a zero numerator for the last shifted step.

Define s(j)=min(r,max(vₚ(j),vₚ(j+1),vₚ(2j+1))). Since p is odd, all denominators have valuation at most s(j) whenever s(j)<r. All factors are then 1 modulo p^(r−s(j)) in the localization. If s(j)=r integrality suffices. Thus W(j+1)−W(j) is divisible by p^(r−s(j)) for either choice of sign.

Set H(t) equal to the sum of 1/i² for 1≤i≤t, omitting multiples of p. Each complete block modulo q=pˢ, s>0, has sum zero modulo q, since multiplying unit residues by 2 multiplies their inverse-square sum by 1/4 and 3 is a unit. Therefore H(j)=0 modulo q if q divides j, and also if q divides j+1 because the extra term is omitted. If q divides 2j+1, the reflection i ↦ 2j+1−i identifies the inverse-square sums on 1,…,j and j+1,…,2j. Their total is a full-block sum, as the next index 2j+1 is omitted. As 2 is a unit this gives H(j)=0 modulo q. Taking s=s(j) gives divisibility of H(j) by p^s(j) in every case.

Summation by parts expresses the sum of W(j)/j² over 1≤j≤N coprime to p as W(N) H(N) minus the sum of (W(j+1)−W(j)) H(j) over 1≤j<N. Every term on the right is divisible by pʳ. Multiplication by N² and, in the shifted row, division by the unit 2 show that both sums of unaligned terms vanish modulo p^(3r). Adding the aligned comparisons proves both assertions.

## Formalization and finite evidence

The direct construction was developed by dwilfand-sys using AI assistance. The upstream Lean statement is by @sntntHb. The formal draft reuses @TheWaler’s implementation of the Robert–Zuber ratio and adapts inverse-square and summation-by-parts lemmas from our A181069 work. Project contributor @draonbioetl independently posted a Vandermonde strategy. Coster and Zudilin supply the prior mathematical results described above.

The accompanying exact integer checker compares 228 rows over nine primes, 114 choices of parameters, and exponents through 4. It checks 7,098 underlying binomial ratio comparisons, both endpoints, 43,440 adjacent-weight identities, and 43,668 denominator-clearing identities. It also checks Zudilin’s identity separately. Both uniform exponents are sharp at p=5,r=1. The residues modulo 625 are a(5)−a(1) ≡ 125 and a(14)−a(2) ≡ 500. These exact finite checks provide evidence independent of kernel elaboration.

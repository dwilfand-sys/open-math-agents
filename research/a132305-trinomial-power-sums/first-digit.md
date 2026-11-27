# The first p-adic digit of every scaled trinomial coefficient

Put F(x)=1+x+x², t(n,j)=[xʲ]F(x)ⁿ and Aₕ(n)=Σⱼ t(n,j)ʰ. Extend t(n,j) by zero outside the row. Let p≥5 be prime and let Hₚ denote the sum of 1/i² in the field of p elements for 1≤i≤⌊p/3⌋. Write χ for the nontrivial character modulo 3, extended by zero at multiples of 3.

## An explicit formula for the whole row

For every positive n and every nonnegative j, the following quotient is p-integral, and its residue is

$$
\frac{t(pn,pj)-t(n,j)}{(pn)^2}\equiv\frac{H_p}{3}\,t(n-1,j-1)\pmod p. \tag{1}
$$

Thus the first possible p-adic digit in each aligned coefficient is a scalar multiple of the immediately preceding row. Fractions with integer denominators prime to p are interpreted in the localization of the integers at p. In particular the displayed quotient need not be an ordinary integer.

For m≥1 prime to p, r≥1 and h≥3 put b=vₚ(h), u=h/pᵇ and

$$
B_h(m)=\sum_j t(m,j)^{h-1}t(m-1,j-1).
$$

The following integral quotient gives the corresponding moment digit:

$$
\frac{A_h(mp^r)-A_h(mp^{r-1})}{p^{2r+b}}\equiv u\,m^2\chi(p)^{r-1}\,\frac{H_p}{3}\,B_h(m)\pmod p. \tag{2}
$$

Any nonzero residue in (1) or (2) gives equality in its lower bound on the valuation.

In particular Bₕ(1)=1. At p=5 the scalar H₅/3 is 2 modulo 5, and at p=7 the scalar H₇/3 is 1 modulo 7. For every h≥3 and both of those primes, vₚ(Aₕ(pʳ)−Aₕ(p^{r−1}))=2r+vₚ(h) at every level. Thus a bound of 3r fails for infinitely many r at these fixed primes, for each fixed h. When h=2 the right side of (2) carries an additional factor 2. Indeed A₂(n)=t(2n,2n) and B₂(m)=t(2m−1,2m−1) by symmetry and convolution, so this special case is the central coefficient theorem of Pan and Sun.

## The polynomial that propagates the first digit

For a series U=Σ uⱼxʲ write Cₚ(U)=Σ uₚⱼxʲ. Suppose G is an integral polynomial or series with constant term 1, and

$$
L=\log G(x)-\frac1p\log G(x^p)
$$

lies in xℤ₍ₚ₎[[x]] with Cₚ(L)=0. Define the p-integral series Eₚ(G)=(Cₚ(Gᵖ)−G)/p². Then for every positive n,

$$
\frac{C_p(G^{pn})-G^n}{(pn)^2}\equiv G^{n-1}E_p(G)\pmod p. \tag{3}
$$

If G is polynomial, Eₚ(G) is polynomial. The hypothesis holds for a product of factors (1−xᵈ) to integral powers with p∤d.

For the proof use G(x)^{pn}=G(xᵖ)ⁿ exp(pnL) and Cₚ(U(xᵖ)V(x))=U(x)Cₚ(V(x)). The term linear in L vanishes exactly. For k≥3 one has vₚ(k!)≤k−3. This follows immediately for k=3, and for k≥4 use vₚ(k!)≤(k−1)/(p−1)≤k−3. Writing r=vₚ(pn), each k≥3 term has valuation at least 3r. Consequently

$$
\frac{C_p(G^{pn})-G^n}{(pn)^2}\equiv\frac12G^n C_p(L^2)\pmod {p^r}.
$$

The case n=1 gives Eₚ(G)≡G Cₚ(L²)/2 modulo p. Multiplication by G^{n−1} proves (3). Each fixed coefficient involves finitely many terms.

At G=F, the endpoints of Cₚ(Fᵖ)−F vanish exactly and its degree is at most two. Hence Eₚ(F)=x(t(p,p)−1)/p² over the rationals. The central constant is known by the n=1 case of the theorem of Hao Pan and Zhi-Wei Sun. There is also a direct harmonic computation.

In the latter computation, L=Σ_{p∤i} cᵢxⁱ/i with cᵢ=1−3·1_{3∣i}. For M=pj>0 the coefficient of xᴹ in L² is, modulo p, the negative of the sum of cᵢc_{M−i}/i² on 1≤i<M, omitting multiples of p. When 3∣j, the interval consists of full blocks modulo 3p with the zero endpoint omitted. Each residue class modulo 3 contributes zero because 1/i² sums to zero over the units modulo p. When 3∤j, the two classes i≡0,M modulo 3 are disjoint and exchange under i↦M−i. The unweighted complete-block sum again vanishes. The remaining value is six times the sum of 1/i² on multiples of three. It equals (2/3) times the inverse-square sum through ⌊pj/3⌋, omitting multiples of p. Full p-blocks have zero sum. For j≡1 this leaves Hₚ, and for j≡2 it leaves −Hₚ by reflection. Thus [xʲ]Cₚ(L²)=(2/3)χ(j)Hₚ modulo p. Finally Σ_{j≥1}χ(j)xʲ=x/F(x), giving (1) from (3).

## From single coefficients to moments

Put N=mpʳ, n=N/p and write δⱼ=t(N,pj)−t(n,j), of valuation at least 2r. The term linear in δⱼ in the power difference is h t(n,j)^{h−1}δⱼ. For q≥2, vₚ(C(h,q))≥b−vₚ(q) follows from q C(h,q)=h C(h−1,q−1). Hence the terms of degree q≥2 are divisible by p^{2r+b+1}, since 2r(q−1)−vₚ(q)≥1. If p∤k, coefficient extraction from (Fᴺ)'=NF'F^{N−1} shows pʳ∣t(N,k). For h≥3, r(h−2)≥b+1, so its h-th power also vanishes at this precision. Using (1) leaves the factor Bₕ(n).

To reduce that factor, put Q=p^{r−1}. Modulo p one has F(x)ⁿ=F(x^Q)ᵐ. Thus the only potentially nonzero terms of Bₕ(n) have index j=Qk. Since xF(x)^{n−1}=F(x)ⁿ Σ_{d≥1}χ(d)xᵈ, the coefficient of x^{Qk} reduces to Σ_{d=1}^k t(m,k−d)χ(Qd)=χ(Q)t(m−1,k−1). The other factor reduces to t(m,k)^{h−1}. This proves (2).

## Exactly which integral polynomials have a quadratic aligned bound

Fix a single prime p≥5. For G∈ℤ[x] with G(0)=1 and degree d, the following are equivalent.

1. G is a product of cyclotomic polynomials of orders prime to p, each normalized to have constant term 1, with repetitions allowed.
2. Its reduced logarithm has zero coefficients at all positive exponents divisible by p.
3. For all positive n and all j≥0, the valuation of [x^{pj}]G(x)^{pn}−[xʲ]G(x)ⁿ is at least 2vₚ(pn).
4. The same bound holds at each fixed j=1,…,d along an unbounded sequence of n=pᵏ. The sequence can depend on j.

The constant polynomial 1 satisfies these conclusions as an empty product. For (1)⇒(2) expand the cyclotomic factors as products of (1−xᵉ) with p∤e. This also proves p-integrality of the reduced logarithm. The above expansion proves (1)⇒(3), and (3)⇒(4) is immediate.

For necessity write G=∏ᵢ(1−αᵢx) over the complex numbers and Sⱼ=Σᵢαᵢʲ. All d reciprocal roots are nonzero. Condition (2) implies Sₚⱼ=Sⱼ for j≤d. Conversely, suppose (4) holds. For fixed j≥1 let Dⱼ(u)=[x^{pj}]G(x)^{pu}−[xʲ]G(x)ᵘ. This is a rational polynomial in u by the finite binomial expansion at the given coefficient. It vanishes at 0 and D'ⱼ(0)=(Sⱼ−Sₚⱼ)/j. The quotient Dⱼ(pᵏ)/pᵏ tends p-adically to D'ⱼ(0). By (4) it tends to zero, so the same power-sum equalities follow. Newton's identities for j=1,…,d identify the two multisets {αᵢ} and {αᵢᵖ}, with multiplicities. The p-power map permutes their finite support. Every αᵢ therefore has an order dividing pᵉ−1 for some e≥1. Rational factorization yields (1).

This also gives an exact alternative when (1) fails. Some index 1≤j≤d has D'ⱼ(0)≠0; at that one fixed j, the difference has valuation exactly k+vₚ(D'ⱼ(0)) for every sufficiently large n=pᵏ. This follows directly from the same p-adic limit and the discreteness of the valuation. Thus finitely many fixed column tests suffice for necessity at one prime.

## Exact limiting slopes and the cubic obstruction

Every integral polynomial G with G(0)=1 satisfies the uniform aligned lower bound vₚ([x^{pj}]G^{pn}−[xʲ]Gⁿ)≥vₚ(pn). Indeed, G(x)ᵖ≡G(xᵖ) mod p, and raising congruent elements to the p-th power raises a positive p-adic congruence exponent by at least one. Raising to n gives the claimed precision.

Now suppose G is nonconstant and its reciprocal roots are all roots of unity of orders prime to p. Let M be the least common multiple of their orders and let d=deg G. At the fixed coefficient j=M, the rational polynomial D_M(u) of the preceding section has zero constant and linear coefficients. Its quadratic coefficient is

$
\frac{p^2}{2}[x^{pM}]L^2
=\frac{p^2}{2}\sum_{\substack{1\le i<pM\\p\nmid i}}
 \frac{S_i^2}{i(pM-i)}>0.
$

Indeed, expand G(xᵖ)ᵘ(exp(puL)−1) as a power series in u and take the coefficient at x^{pM}. The mixed term log G(xᵖ)·L contributes zero by its support. At p∤i the coefficient of L is −Sᵢ/i. As the multiset of roots is closed under complex conjugation and every root has order dividing M, one has S_{pM−i}=S_{−i}=Sᵢ, a real number. Every summand is nonnegative. The term i=M occurs and S_M=d, so the sum is strictly positive.

Write c for this nonzero quadratic coefficient. Then D_M(pᵏ)/p^{2k} tends to c p-adically. Its valuation is exactly 2k+vₚ(c) for all sufficiently large k. In particular, even a polynomial with Eₚ(G)=0 modulo p cannot have a uniform cubic bound over all coefficient indices and row levels. Combining the two limiting slopes gives the complete distinction for p≥5. A polynomial with a bad-order or non-root-of-unity reciprocal root has maximal uniform exponent 1. A nonconstant p-good cyclotomic product has maximal uniform exponent 2. The constant polynomial 1 has zero difference everywhere. Here a uniform exponent e means divisibility by p^{e·vₚ(pn)} for all n and all j; the two fixed-column limits also rule out larger real slopes even after allowing a fixed additive loss.

For example, this result is compatible with the classical high-order binomial congruences whose *column as well as row* is repeatedly scaled by p. Here the comparison at row n=pᵏ always includes the fixed column j=M, while its upper-row index is pM.

The onset of the exact slope is effective. Each coefficient of the rational polynomial Dⱼ(u) has denominator dividing (pj)!, since it is an integer linear combination of coefficients in C(pu,l) and C(u,l) with l≤pj. If c·uᵉ is its first nonzero term, let a=vₚ(c) and b=vₚ((pj)!). For each k>b+a the higher terms have strictly larger valuation than c·p^{ek}, hence vₚ(Dⱼ(pᵏ))=ek+a. Together with the root orders or Newton sums this gives a finite procedure to produce a counterexample to any proposed larger uniform exponent.

## Attribution and independent verification

Peter Bala stated the quadratic moment conjectures on OEIS [A132303](https://oeis.org/A132303), [A132304](https://oeis.org/A132304), and [A132305](https://oeis.org/A132305). The [A132303 cube argument](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md) and [cyclotomic quadratic theorem](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/CyclotomicRationalFramingTower.md) by @rbajaj5 already supply the logarithm and its support. That author's [Euler-product note](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/EulerProductCubicCartierMoments.md) explicitly isolates the quadratic Cartier term and controls the higher exponential terms in a different family.

[Pan and Sun, Theorem 1.1 and Corollary 1.1](https://arxiv.org/abs/2012.05121), established (1) on the central column, expressing the constant by a Bernoulli polynomial. The pure-power result for m=1 in (2) is also recoverable from their central result and the known quadratic coefficient bound, since the endpoints of each row agree exactly. The manuscript gives the all-column formula, its general moment version, the polynomial propagation identity and the finite-column converse. The classification is related to [Müller on rational 2-functions](https://arxiv.org/abs/2006.06388) and [Beukers, Houben and Straub on rational Gauss congruences](https://arxiv.org/abs/1710.00423). Historical priority for the statements here is unestablished.

The direct checker also verified the distinct h=2 factor in all 241 cases. The direct checker tested 33,557 aligned coefficients, all endpoints, and 4,105 moment comparisons across 12 primes, 241 parameter triples and exponents through r=6. Of these, 1,446 had p∣h and 723 had p²∣h. A separate checker based on a derivative recurrence tested 11,279 aligned coefficients and 641 moment comparisons, including 180 with p∣h. The polynomial-slope checker separately verified 60 eventual valuations through k=11 on ten polynomial/prime cases, covering good cyclotomic roots, bad cyclotomic orders, and non-cyclotomic roots. These exact computations complement the arguments. No kernel check of these refinements is claimed.

# Strongly nontriangular integers with boundedly many prime factors

The sieve in [the infinitude draft](Infinitude.md) admits a power-sized roughness cutoff. In particular there exist absolute constants $\delta,c>0$ such that for every sufficiently large $X$ there are at least

$$
cX/(\log X)^{5/2}
$$

squarefree strongly nontriangular numbers $n=2p-1$, with $X<p\le2X$, $p\equiv1\bmod3$ prime, whose least prime factor exceeds $X^\delta$. All prime factors of $4p+1$ may simultaneously be required to be $1\bmod4$. In particular these $n$ have at most some fixed number of prime factors, independent of $X$.

The proof below refers to the arithmetic and integer Selberg arguments in Sections 1 and 4 of the infinitude draft. It replaces the polylogarithmic presieve from Section 2. The smaller count buys a bound on the number of prime factors.

Let $0<\eta<1/10$ be fixed temporarily, and put $z=X^{1/(2+\eta)}$, $D_1=X^{1/2-\eta/16}$, $D_0=X^{\eta/32}$. Choose a large fixed number $U>10$, to be specified, and take

$$
\delta=\eta/(32U),\qquad y=X^\delta.
$$

Choose $U$ large enough that $\delta<1/1000$. As in the infinitude draft, for $5\le t\le y$ exclude $2^{-1}\bmod t$ and, when $t\equiv3\bmod4$, exclude also $-4^{-1}\bmod t$. For $y<t<z$, sieve only primes $t\equiv3\bmod4$ and exclude only $-4^{-1}$. Write $A,B$ for the two indicators on the range primes $p\equiv1\bmod3$. As before the two small-prime roots are distinct, all roots are units, and the disjoint prime ranges yield a multiplicative CRT main term.

Use upper/lower beta weights $A^\pm$ for the first group and $B^\pm$ for the second. For the first group the multiplicative excluded density is $h_0(t)=(1+1_{t\equiv3\ (4)})/(t-1)$, and its local product $V_0$ satisfies the upper-dimensional condition with $\kappa=2$ and absolute constant, by Mertens in fixed progressions (even the bound $\kappa=3/2$ holds). The fundamental lemma for beta weights of parameter $\beta=9$ and level $D_0=y^U$ gives for each sign

$$
\mathcal A^\pm=V_0(1+O(U^{-U/2})),
$$

where $\mathcal A^\pm$ denotes the corresponding weighted local main sum. See Kurlberg, Lester and Rosenzweig, Theorem 2.2, reproducing Friedlander–Iwaniec, *Opera de Cribro*, Lemma 6.11. The constant depends only on the fixed dimension and dimension bound. For the other group let $\mathcal B^\pm$ denote its local main sums and $V_1$ its local product. The half-dimensional sieve with $s=\log D_1/\log z$ from Section 3 of the infinitude draft gives

$$
\mathcal B^-\ge c_0\sqrt{\eta}\,V_1,\qquad
0\le\mathcal B^+\le C_0 V_1
$$

for sufficiently large $X$ depending on $\eta$, with absolute $c_0,C_0>0$. Both upper local sums are nonnegative, being averages under independent local Bernoulli events.

Apply the pointwise bound

$$
AB\ge A^+B^--(A^+-A^-)B^+.
$$

Here each bracket is interpreted as the summed divisor weight evaluated at the integer's forbidden-prime product. The inequality follows from $A^+,B^+\ge0$, $B^-\le B\le B^+$ and $A^-\le A\le A^+$. The modulus in the expansion is bounded by $3D_0D_1=3X^{1/2-\eta/32}$. Divisor-weighted Bombieri–Vinogradov applies because the beta coefficients have absolute value at most one, the two factors of the modulus are separated by their prime ranges, and the admissible number of CRT roots is divisor-bounded. Thus summation over primes gives at least

$$
M\big[\mathcal A^+\mathcal B^-
 -(\mathcal A^+-\mathcal A^-)\mathcal B^+\big]
 -O_{\eta,U}(X/(\log X)^{10}),
$$

where $M=(\pi(2X)-\pi(X))/2$. Choose $U$ sufficiently large in terms of $\eta$ so that the main term is at least $(c_0/2)M V_0V_1\sqrt\eta$. The Euler product obeys $V_0V_1\asymp1/(\log y\sqrt{\log z})$ with absolute constants for all sufficiently large $X$. Consequently the lower bound before removing large inert factors is $c_1\sqrt\eta\, X/((\log X)^{3/2}\log y)$, with $c_1>0$ absolute.

In the switched upper bound (Section 4), $Y\ge z$ and $b=Y^{1/400}$, so $y<b$ holds for every allowed $\eta,\delta$ above. The three root counts, the Selberg denominator, and the two harmonic sums therefore give the same upper bound $C_1\eta^{3/2}X/((\log X)^{3/2}\log y)$ plus a power-saving error, with absolute $C_1$. Choose $\eta$ sufficiently small that $C_1\eta<c_1/2$, then fix $U$ as above. Subtracting leaves $\gg X/((\log X)^{3/2}\log y)\gg X/(\log X)^{5/2}$ candidate primes.

By Section 1 all representable candidates have a triangle gcd $g>y$, and their count is $O(X\log X/y)$. The number divisible by $r^2$ for any prime $r>y$ is at most $4X\sum_{r>y}r^{-2}=O(X/y)$, and all smaller prime divisors are excluded. Both errors are negligible. Finally, if $n$ has $k$ prime factors counted with multiplicity, $X^{\delta k}<n<4X$, so $k\le\lceil2/\delta\rceil$ for all sufficiently large $X$. No explicit small value of this absolute integer is asserted.

The quantitative prime-factor conclusion is a paper result. The authors of the cited sieve theorems supply the analytic inputs, and the application to the triangle sequence is a Codex research draft for @dwilfand-sys. It has no verified historical priority or kernel verdict.

* [Kurlberg, Lester and Rosenzweig, Theorems 2.1 and 2.2](https://kurlberg.github.io/eprints/2dscar.pdf)
* [Nath and Xie, Lemmas 3.2 and 3.6](https://arxiv.org/pdf/2501.16723)
* [Petersen, Validashti and Wayland, Strongly Nontriangular Numbers](https://doi.org/10.1080/0025570X.2026.2627861)

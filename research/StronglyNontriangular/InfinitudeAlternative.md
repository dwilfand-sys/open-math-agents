# An independent sieve argument for infinitude in A400795

This research draft gives a second route through the large-prime subtraction. It uses a shrinking parameter in the quantitative half-dimensional beta sieve. The other draft uses a fixed parameter and retains the roughness condition when switching. Neither draft has a Lean kernel certificate or independent expert review.

Write $P(i,j)=(ij+i+j-\gcd(i,j))/2$, with $i,j\ge2$. As shown below, the number of integers up to $4X$ omitted from the range of $P$ is

$$
\gg X / ((\log X)^{3/2}(\log\log X)^2).
$$

Use primes $X<p\le 2X$ with $p\equiv1\pmod3$, and put $m=4p+1$, $n=2p-1$. Set

$$
L=\log\log X,\qquad \eta=L^{-2},\qquad y=(\log X)^4,
\qquad z=X^{1/(2+\eta)},\qquad D=X^{1/2-\eta/16}.
$$

## The lower bound

Presieve the primes $5\le t\le y$ by excluding the class $2p=1\pmod t$, and also $4p=-1\pmod t$ when $t\equiv3\pmod4$. These are one or two distinct nonzero classes, since their possible collision implies $t\mid3$. Write $h_0(t)=(1+1_{t\equiv3\ (4)})/(t-1)$. On the disjoint set of primes $y<t<z$, $t\equiv3\pmod4$, exclude only the latter class, so $h_1(t)=1/(t-1)$. The progression modulo 3 needs no sieving at 2 or 3. All conditional densities over squarefree moduli are multiplicative by CRT.

Let $A,B$ be the two indicators. Use the even and following odd Bonferroni truncations $A^+,A^-$, with even truncation order $R=2\lceil10L\rceil$, and support at most $y^{R+1} = \exp(O(L^2))$. For $V_0=\prod(1-h_0(t))$, both CRT-weighted main terms differ from $V_0$ by at most their gap

$$
\sum_{t_1<\cdots<t_{R+1}}\prod h_0(t_i)
\le\left(\frac{e\sum h_0(t)}{R+1}\right)^{R+1}
\ll (\log X)^{-10}.
$$

Indeed, $\sum h_0(t)=O(\log\log y)=O(\log L)$. The Euler product lies between the two Bonferroni truncations by independence in the finite product of Bernoulli probability spaces.

Take $B^+,B^-$ as the upper and lower half-dimensional beta-sieve weights at level $D$. With $V_1=\prod(1-h_1(t))$, their CRT-weighted main terms satisfy the usual upper bound $V_1(F(s)+O((\log D)^{-1/6}))$ and lower bound $V_1(f(s)-O((\log D)^{-1/6}))$, respectively. Here

$$
s=(2+\eta)(1/2-\eta/16)=1+3\eta/8-\eta^2/16.
$$

The half-dimensional beta-sieve estimate is uniform here. Its product hypothesis is the upper bound $V(w)/V(v)\le(\log v/\log w)^{1/2}(1+C/\log w)$ on each interval $w\le t<v$. Dropping primes up to $y$ only decreases the left side. The corresponding bound without dropping primes follows from Mertens in the residue class 3 modulo 4, and the summable difference between $1/(t-1)$ and $1/t$. The factor $F(s)$ is bounded near 1, and $f(s)\gg\sqrt{s-1}\gg1/L$. See Nath and Xie, arXiv:2501.16723v3, Lemma 3.6 and section 5, quoting Friedlander and Iwaniec, *Opera de Cribro*, Theorem 11.12. The explicit logarithmic error is $o(1/L)$.

Use the pointwise vector inequality

$$
AB\ge A^+B^--(A^+-A^-)B^+.
$$

In fact $A^+,B^+\ge0$, and replacing $B^-$ by $B$, then $B^+$ by $B$, bounds the right side above by $A^-B\le AB$. After summing over primes, CRT factors the weighted main terms. The joint modulus is at most $3D y^{R+1}\le X^{1/2}(\log X)^{-C}$ for each fixed $C$ and sufficiently large $X$. All residues are reduced. Each small prime in a modulus allows at most two choices, and the two sets of prime factors are disjoint, so the errors have divisor-bounded multiplicity. Divisor-weighted Bombieri–Vinogradov gives total error $O(X/(\log X)^{10})$, by Nath and Xie, Lemma 3.2 with one prime factor. Its center can equivalently be the dyadic prime count divided by the totient, since all range primes exceed the moduli.

The unrestricted prime main scale before sieving is $M=(\pi(2X)-\pi(X))/2\asymp X/\log X$. Mertens for primes and the progression modulo 4 gives

$$
V_0V_1\asymp \frac1{\log y\sqrt{\log z}}.
$$

For the small inert primes the joint factor $1-2/(t-1)$ differs from $(1-1/(t-1))^2$ by a factor $1+O(t^{-2})$. Thus the number of primes satisfying both truncated sieves is $\gg X/((\log X)^{3/2}L^2)$.

## Removing the remaining inert primes

Since $m\equiv1\pmod4$, any remaining inert prime factors have even total multiplicity. Since $z^3>8X+1$, there are exactly two, counted with multiplicity, for every exception. Write $m=kqr$, $z\le q\le r$, where $q,r\equiv3\pmod4$ are primes and $k$ is supported on primes $1\pmod4$. Then $k\le K=(8X+1)/z^2$, $q\le\sqrt{8X+1}$.

Drop the roughness of $n$. For fixed $k,q$ in the actual range $kq^2\le8X+1$, put $Y=(8X+1)/(kq)\ge z$. Count integers $r=4a+3\le Y$ for which both $r$ and $p=(kqr-1)/4$ are prime and $r\ge q\ge z, p>X$. The two integer linear forms $4a+3$ and $kqa+(3kq-1)/4$ have determinant $-1$. For each odd prime $t\nmid kq$ they exclude two distinct residue classes, and for $t\mid kq$ just one. After ignoring 2 the Selberg upper bound sieve gives uniformly

$$
\ll \frac{Y}{(\log X)^2}\prod_{t\mid kq,\ t>2}\left(1+\frac1{t-2}\right).
$$

For detail, sift to $b=Y^{1/400}$, and put $E=Y^{1/20}$. For each selected prime $t\le b$, write $\nu(t)$ for its one or two forbidden classes. The Selberg denominator $G(E)=\sum_{d\le E,\ d\mid\prod t}\prod_{t\mid d}\nu(t)/(t-\nu(t))$ is at least half the untruncated Euler product for large $Y$. Under the normalized product, the expected $\log d$ is $\sum\nu(t)\log(t)/t\le (2+o(1))\log b$, and Markov suffices. Its reciprocal is bounded by the displayed Euler correction times $O((\log b)^{-2})$, by Mertens. The standard Selberg error for interval residue counts is $O(\sum_{l\le E^2}3^{\omega(l)}\nu(l))=O(E^2(\log E)^5)$, absorbed in $Y/(\log X)^2$. The actual primes being counted exceed $b$. Throughout $\log Y\asymp\log X$.

The factor associated with $q\ge z$ is bounded. Partial summation with the prime number theorem gives

$$
\sum_{z\le q\le\sqrt{8X+1}}\frac1q
\ll \log\left(\frac{\log\sqrt{8X+1}}{\log z}\right)+\frac1{\log X}
\ll \eta.
$$

The same inequality follows directly from Chebyshev's upper bound for the endpoint and the integral. The remaining harmonic sum, with $H(k)=\prod_{t\mid k}(1+1/(t-2))$, satisfies

$$
\sum_{k\le K,\ t\mid k\Rightarrow t\equiv1\ (4)}\frac{H(k)}k
\le \prod_{t\le K,\ t\equiv1\ (4)}\left(1+\frac{1+1/(t-2)}{t-1}\right)
\ll\sqrt{\log(2K)}\ll\sqrt{\eta\log X}.
$$

Multiplying yields $O(X\eta^{3/2}/(\log X)^{3/2})=O(X/((\log X)^{3/2}L^3))$ exceptions. Thus $\gg X/((\log X)^{3/2}L^2)$ candidates remain for which $m$ contains no inert primes and $n$ has no prime factor $\le y$.

## Removing all representations

If $n=P(i,j)$ with $\gcd(i,j)=1$, then $(i+1)(j+1)=4p$. Since each factor is at least 3, the unique unordered possibility for large $p$ is the pair $4,p$. But $3\mid p-1$, violating the gcd. If the gcd is 2, write $i=2a,j=2b$ with $(a,b)=1$. Then $n=2ab+a+b-1$, so oddness makes both $a,b$ odd and $m=(2a+1)(2b+1)$. Each factor is 3 modulo 4 and therefore has an inert prime, impossible.

Every other gcd $g$ divides $2n$. Because $n$ is odd and has no prime factor at most $y$, a divisor $g>2$ of $2n$ exceeds $y$. Write $i=ga,j=gb$. Now $2n=g^2ab+g(a+b-1)\ge g^2ab$. Over all $n\le 4X$, the number of represented integers with such a gcd is at most

$$
\sum_{g>y}\sum_{ab\le 8X/g^2}1
\ll X\log X\sum_{g>y}g^{-2}
\ll X/(\log X)^3.
$$

This is smaller than the surviving count. Distinct primes yield distinct integers. The claimed lower bound and infinitude follow.

## Sources

* Nath and Xie, *Almost primes and primes that are sums of two squares plus 1*, arXiv:2501.16723v3, https://arxiv.org/pdf/2501.16723. The proof above uses their statements of scalar beta-sieve estimates and a weighted Bombieri–Vinogradov estimate. Their comparable-cutoffs vector proposition is not invoked.
* T. Kyle Petersen, Javid Validashti and Chase Wayland, *Strongly Nontriangular Numbers*, Mathematics Magazine (2026), https://doi.org/10.1080/0025570X.2026.2627861. [OEIS A400795](https://oeis.org/A400795) records the infinitude conjecture.

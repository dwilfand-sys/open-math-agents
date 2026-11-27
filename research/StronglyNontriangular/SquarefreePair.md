# Squarefree strongly nontriangular numbers with a squarefree split neighbor

For \(a,b\ge2\), put \(P(a,b)=(ab+a+b-\gcd(a,b))/2\). Petersen, Validashti and Wayland conjectured that infinitely many positive integers are strongly nontriangular. We use the convention of Kyle Petersen's OEIS entry A400795, which counts 1 as generalized triangular. [Original problem](https://doi.org/10.1080/0025570X.2026.2627861) · [OEIS A400795](https://oeis.org/A400795)

**Theorem.** For some absolute \(c>0\), every sufficiently large \(X\) admits at least
\[
 c\,\frac{X}{(\log X)^{3/2}\log\log X}
\]
primes \(X<p\le2X\), \(p\equiv1\bmod3\), for which \(n=2p-1\) is strongly nontriangular, the product \((2p-1)(4p+1)\) is squarefree, and every prime divisor of \(4p+1\) is \(1\bmod4\). We can also require that every prime divisor of \(2p-1\) exceed \((\log X)^4\).

The main-rate [infinitude proof](Infinitude.md) imposes the roughness of \(2p-1\) and the class restriction at \(4p+1\). The change here is to exclude the squares of small split primes in \(4p+1\) during its initial sieve. Simply discarding multiples of small prime squares after sifting does not give the conclusion at this scale.

## Local restrictions and the distribution estimate

Write \(n=2p-1,\ N=4p+1,\ y=(\log X)^4,\ z=X^{1/(2+\eta)},\ D=X^{1/2-\eta/16}\), where \(0<\eta<1/10\) is fixed for now. The two forms are odd and are \(1,2\bmod3\), respectively. Since \(N-2n=3\), \(\gcd(n,N)=1\). It suffices to enforce squarefreeness for each form separately.

For every prime \(5\le\ell\le y\) exclude \(p\equiv2^{-1}\bmod\ell\), which is the condition \(\ell\mid n\). At \(\ell\equiv3\bmod4\) also exclude \(p\equiv-4^{-1}\bmod\ell\), or \(\ell\mid N\). At \(\ell\equiv1\bmod4\) instead exclude the single class \(p\equiv-4^{-1}\bmod\ell^2\), or \(\ell^2\mid N\). All these roots are units at their stated moduli. The first root modulo \(\ell\) cannot coincide with the reduction of the second: after multiplication by 4 equality would give \(2=-1\bmod\ell\). The local density of the union among reduced prime classes is therefore
\[
 h_\ell =
 \begin{cases}
 2/(\ell-1),&\ell\equiv3\bmod4,\\
 1/(\ell-1)+1/(\ell(\ell-1)),&\ell\equiv1\bmod4.
 \end{cases}
\]
For split primes, the ratio between the new survival probability and \(1-1/(\ell-1)\) is \(1-1/[\ell(\ell-2)]\). The product of these ratios is bounded below by an absolute positive constant, because every factor is positive and the sum of their losses converges. Thus \(V_*=\prod_{5\le\ell\le y}(1-h_\ell)\asymp(\log y)^{-3/2}\) with absolute constants.

Let \(\mathcal B_*\) be the integers \(N\) from the surviving primes, and \(M=(\operatorname{li}(2X)-\operatorname{li}(X))/2\). For squarefree \(d\) supported on the primes \(\ell>y,\ \ell\equiv3\bmod4\), forcing \(d\mid N\) imposes one reduced class at each prime of \(d\). For every fixed \(A>0\),
\[
 |\{N\in\mathcal B_*:d\mid N\}|=\frac{M V_*}{\varphi(d)}+R_d,\qquad
 \sum_{d\le D}|R_d|\ll_{\eta,A}X(\log X)^{-A},
\]
with the sum over these \(d\). Here is the prime-power detail in the error bound. Put \(J=2\lceil\log\log X\rceil\). In each of the order-\(J\) and order-\(J+1\) Bonferroni sums, select a set of at most \(J+1\) distinct small primes and at each one of the two disjoint forbidden alternatives. Its term counts exactly one reduced residue class modulo
\[
 m=3d\prod_{\ell\text{ selected}}\ell^{e_\ell},\qquad
 e_\ell=2 \text{ only for the split square-divisibility alternative, otherwise }e_\ell=1.
\]
CRT gives the main term \(M/(\varphi(d)\prod_{\ell\ {\rm selected}}\varphi(\ell^{e_\ell}))\) for that class. Hence summing the alternatives at each selected prime gives the product of the \(h_\ell\). The two Bonferroni main sums bracket \(V_*\) and differ by at most \((\mathrm e\sum h_\ell/(J+1))^{J+1}\ll_B(\log X)^{-B}\) for every fixed \(B\), since \(\sum h_\ell=O(\log\log y)\). The harmless sum of \(1/\varphi(d)\) up to \(D\) is \(O(\log X)\).

All moduli satisfy \(m\le3Dy^{2(J+1)}\le X^{1/2-\eta/32}\) for sufficiently large \(X\). Given \(m\), the factor \(d\), the set of small primes, and all split-prime alternatives are fixed: an exponent two is precisely the split square condition. An inert small prime of exponent one can give either sign, so the multiplicity for fixed \(m\) is at most \(2^{\omega(m)}\) in each Bonferroni sum. Bombieri–Vinogradov applies to all integer moduli in this range, including nonsquarefree ones. If \(E(m)\) denotes the maximum prime progression-count error on \((X,2X]\), use \(E(m)\ll X/\varphi(m)\) (here \(m<X^{1/2}\)) and Cauchy–Schwarz as in the main proof. The required Euler bound is valid even after including every prime power:
\[
 \sum_{m\le X}\frac{4^{\omega(m)}}{\varphi(m)}
 \ \le\prod_{\ell\le X}\left(1+4\sum_{a\ge1}\frac1{\varphi(\ell^a)}\right)
 =\prod_{\ell\le X}\left(1+\frac{4\ell}{(\ell-1)^2}\right)
 \ll(\log X)^4 .
\]
Choosing an arbitrarily large power saving in the unweighted Bombieri–Vinogradov estimate proves the claimed summed error.

## Switching and the last square divisors

For inert primes \(y<\ell<z\), the density remains \(1/(\ell-1)\). The same dimension bound and Matomäki's Lemma 2 therefore give at least
\[
 c_1\sqrt\eta\,\frac{X}{(\log X)^{3/2}\log y}
\]
survivors, with absolute \(c_1>0\) and \(X\) sufficiently large depending on \(\eta\). The additional exclusions only reduced the constant in \(V_*\). Each survivor with remaining inert factors still has \(N=kqr\), with exactly two inert prime factors \(q,r\ge z\) counted with multiplicity. These primes form a subset of the switched configurations already bounded in §4 of the [infinitude proof](Infinitude.md). In detail, for \(H=kq\), the switched integer \(r\) avoids \(0,H^{-1}\) modulo sieving primes \(\ell\nmid H\), as forced by primality of \(r,p=(Hr-1)/4\); below \(y\) it also avoids \(3H^{-1}\), by roughness of \(n=(Hr-3)/2\). A prime dividing \(H\) leaves only root zero. The three roots are distinct for \(\ell\ge5\). Dropping the new square restrictions in this upper bound leaves it valid and gives the same absolute upper constant \(C\) multiplying \(\eta^{3/2}X/((\log X)^{3/2}\log y)\), plus a negligible error. Choose \(\eta\) so that \(C\eta<c_1/2\). This proves the desired count before checking large prime squares and the remaining representations.

If \(\ell>y\) and \(\ell^2\mid nN\), coprimality of \(n,N\) implies divisibility of one form by \(\ell^2\). For each form there is one residue class for \(p\) modulo \(\ell^2\). Even counting all integers \(p\in(X,2X]\), there are at most
\[
 2\sum_{y<\ell\le\sqrt{8X+1}}\left(\frac{X}{\ell^2}+1\right)
 \ll X/y+\sqrt X .
\]
For \(\ell\le y\), all squares dividing either form have already been excluded. The loss from large squares is therefore negligible.

Finally a representation \(P(a,b)=n\) has \(g=\gcd(a,b)\mid2n\) and \((a+1)(b+1)=2n+g+1\). For \(g=1\), the only eligible factor pair of \(4p\) is \(4,p\); it would give \(\gcd(3,p-1)=3\). For \(g=2\), at least one of \(a/2,b/2\) is odd, hence \(N\) would have a divisor \(3\bmod4\). Every other \(g\) has an odd prime divisor of \(n\), and thus \(g>y\). With \(a=gu,\ b=gv\), a representable \(n\le4X\) gives \(uv\le8X/g^2\). The number of such integers is thus at most \(\sum_{g>y}\sum_{uv\le8X/g^2}1\ll X\log X/y\), also negligible. This proves the theorem.

## Checks and sources

The [exact checker](check_squarefree_pair.py) exhaustively verified the local proportions at the 23 primes from 5 through 97 and four mixed prime-power CRT intersections. For \(75000<p\le150000,\ p\equiv1\bmod3\), with a fixed test roughness cutoff of 19, it found 627 candidates meeting the squarefree and split-factor conditions. Of these, 603 were confirmed strongly nontriangular by directly enumerating all eligible pairs. For instance \(p=75211\) gives \(n=150421=359\cdot419\) and \(N=300845=5\cdot60169\). The difference of 24 illustrates the role of the \(g>y\) estimate. The finite check and the analytical lower bound have different cutoffs.

The analytic foundation is Iwaniec's semilinear sieve and switching method, Matomäki's quantitative half-dimensional bounds, the Bombieri–Vinogradov theorem for primes in progressions, and Selberg's upper-bound sieve. Nath and Xie study a related simultaneous problem for \(p-1,p+2\). Codex derived this squarefree strengthening for @dwilfand-sys on the basis of the linked problem-specific proof. It is a paper proof. Historical priority and machine verification are unconfirmed. [Iwaniec](https://matwbn.icm.edu.pl/ksiazki/aa/aa24/aa2451.pdf) · [Matomäki, Lemma 2](https://users.utu.fi/ksmato/wp-content/uploads/sites/1432/2025/04/Goldbach_k2pl2p1.pdf) · [Gyujin Oh, Selberg sieve, Theorem 1.1](https://web.math.princeton.edu/~gyujino/Selbergsieve.pdf) · [Nath and Xie](https://arxiv.org/abs/2501.16723)

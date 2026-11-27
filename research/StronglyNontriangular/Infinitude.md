# Infinitely many strongly nontriangular numbers

For integers \(a,b\ge2\), write \(P(a,b)=(ab+a+b-\gcd(a,b))/2\). OEIS A400795 consists of integers \(n\ge2\) missing from the image of \(P\). Its definition includes 1 among the generalized triangular numbers by convention. Petersen, Validashti and Wayland conjectured that there are infinitely many strongly nontriangular numbers, and proved infinitude when representations are restricted to coprime \(a,b\).

**Theorem.** For some absolute \(c>0\) and all sufficiently large \(T\), at least
\[
c\,\frac{T}{(\log T)^{3/2}\log\log T}
\]
positive integers \(n\le T\) have no representation \(P(a,b)=n\). These exceptions may all be taken in the form \(2p-1\), with \(p\) prime and \(p\equiv1\bmod3\).

This is a paper argument using classical analytic sieve theorems. The half-dimensional sieve and the switching construction for eliminating two remaining inert prime factors come from Iwaniec's work. Matomäki gives a particularly convenient formulation. The additional roughness condition on \(2p-1\) is imposed twice, before the half-dimensional sieve and inside the switched upper bound. References are given below.

## 1. The arithmetic obstruction

Take \(X<p\le2X\), \(p\equiv1\bmod3\), \(n=2p-1\), \(N=4p+1\), and \(y=(\log X)^4\). Suppose all prime factors of \(n\) exceed \(y\) and all prime factors of \(N\) are \(1\bmod4\). A representation with \(g=\gcd(a,b)\) gives
\[
g\mid2n,\qquad (a+1)(b+1)=2n+g+1.
\]
If \(g=1\), the product on the right is \(4p\). Its only factor pair with both entries at least 3 is \(4,p\), up to order, for \(p>3\). This gives \(\gcd(3,p-1)=3\). If \(g=2\), set \(a=2u,b=2v\), where \(u,v\) are coprime. At least one is odd, so \(N=(2u+1)(2v+1)\) has a divisor \(3\bmod4\). Both possibilities are excluded. Since \(2n\) is divisible by 2 exactly once, any remaining \(g>2\) has an odd prime divisor of \(n\), whence \(g>y\).

With \(a=gu,b=gv\) one has \(2n=g^2uv+g(u+v-1)\). Consequently the number of \(n\le4X\) with any representation with \(g>y\) is at most
\[
\sum_{y<g\le\sqrt{8X}}\ \sum_{uv\le8X/g^2}1
 \ll X\log X\sum_{g>y}g^{-2}\ll X/(\log X)^3.
\tag{1}
\]
It remains to count the primes satisfying the two sets of restrictions.

## 2. The small prime restrictions and their distribution

Call a prime **inert** if it is \(3\bmod4\). Fix \(0<\eta<1/10\), to be chosen later, and put
\[
 z=X^{1/(2+\eta)},\qquad D=X^{1/2-\eta/16},\qquad
 M=\tfrac12(\operatorname{li}(2X)-\operatorname{li}(X)).
\]
On the primes \(X<p\le2X\) with \(p\equiv1\bmod3\), first remove every \(p\) for which a prime \(\ell\le y\) divides \(n\), or an inert prime \(\ell\le y\) divides \(N\). The primes 2 and 3 impose no condition on this progression. Each prime \(5\le\ell\le y\) excludes the unit class \(2^{-1}\bmod\ell\) and, if inert, also \(-4^{-1}\bmod\ell\). The two classes could coincide only for \(\ell=3\). Write \(\nu(\ell)=1+\mathbf1_{\ell\ {\rm inert}}\), \(h(\ell)=\nu(\ell)/(\ell-1)\), with squarefree multiplicative extension. Put
\[
V_0=\prod_{5\le\ell\le y}(1-h(\ell))\asymp(\log y)^{-3/2}.
\tag{2}
\]
Products indexed by \(\ell\) hereafter are over primes. Formula (2) follows from Mertens' estimates for all primes and for the fixed class \(3\bmod4\). Its constants are absolute.

Let \(\mathcal B\) consist of the integers \(N=4p+1\) remaining, and let \(\mathcal P\) be the set of inert primes larger than \(y\). For squarefree \(d\) made from \(\mathcal P\), put \(g(d)=1/\varphi(d)\). We need the following distribution estimate for every fixed \(A>0\), with \(X\) sufficiently large depending on \(\eta,A\):
\[
\#\{N\in\mathcal B:d\mid N\}=MV_0g(d)+R_d,\qquad
\sum_{\substack{d\le D\\d\text{ squarefree, supported on }\mathcal P}}|R_d|
 \ll_{\eta,A} X(\log X)^{-A}.
\tag{3}
\]

Here is a direct verification. Take the even integer \(J=2\lceil\log\log X\rceil\). Apply the even and odd Bonferroni bounds at orders \(J,J+1\) to the small prime exclusions in each count with \(d\mid N\). A term indexed by a squarefree product \(e\) of at most \(J+1\) primes in \([5,y]\) and by \(d\) counts primes in exactly \(\nu(e)=\prod_{\ell\mid e}\nu(\ell)\) reduced residue classes modulo \(3de\), by the Chinese remainder theorem. Its main term is exactly \(Mg(d)h(e)\). The absolute difference between the two alternating local main terms, divided by \(Mg(d)\), is at most
\[
\sum_{\omega(e)=J+1}h(e)
\le\frac{\bigl(\sum_{5\le\ell\le y}h(\ell)\bigr)^{J+1}}{(J+1)!}
\le\left(\frac{\mathrm e\,O(\log\log y)}{J+1}\right)^{J+1}
\ll_A(\log X)^{-A}
\]
for every fixed \(A\). The independent product \(V_0\) lies between these bounds by Bonferroni applied to independent local events. Also \(\sum_{d\le D}g(d)\), over the allowed \(d\), is \(O(\log X)\) by the Euler product.

For the progression errors define \(E(m)\) as the maximum over reduced classes modulo \(m\) of the absolute difference between the prime count on \((X,2X]\) and \((\operatorname{li}(2X)-\operatorname{li}(X))/\varphi(m)\). All moduli above satisfy
\[
3de\le3D y^{J+1}\le X^{1/2-\eta/32}
\]
for \(X\) sufficiently large. The factorization \(m=3de\) is uniquely determined by its prime ranges, and \(\nu(e)\le2^{\omega(m)}\). The usual Bombieri–Vinogradov bound gives \(\sum E(m)\ll_B X(\log X)^{-B}\) over this range for any fixed \(B\). Its divisor-weighted version follows from Cauchy–Schwarz with factors \(E(m)^{1/2}\) and \(2^{\omega(m)}E(m)^{1/2}\). In the second moment use \(E(m)\ll X/\varphi(m)\) and
\(\sum_{m\le X,\ {\rm squarefree}}4^{\omega(m)}/\varphi(m)\ll(\log X)^4\) by the Euler product. Taking \(B\) sufficiently large proves (3), including errors from either Bonferroni bound.

## 3. Sifting the inert prime factors

Apply the Rosser–Iwaniec sieve of dimension \(1/2\) to the actual positive sequence \(\mathcal B\), the primes of \(\mathcal P\) below \(z\), and level \(D\). Its local product satisfies
\[
V_1=\prod_{\substack{y<\ell<z\\\ell\ {\rm inert}}}
  (1-1/(\ell-1))\asymp\left(\frac{\log y}{\log z}\right)^{1/2}.
\]
For the sieve's dimension hypothesis the full inert product over \(w\le\ell<u\), omitting 3, is at most \((\log u/\log w)^{1/2}(1+K/\log w)\) with absolute \(K\), by the prime number theorem in the fixed classes modulo 4 and partial summation. Deleting primes up to \(y\) can only decrease this product of reciprocals of survival probabilities. Thus the same \(K\) works when the lower cutoff \(y\) varies. All comparison constants for \(V_1\) are absolute.

Specifically, Matomäki's Lemma 2 gives lower and upper main factors \(f_{1/2}(s)+o_K(1)\) and \(F_{1/2}(s)+o_K(1)\) multiplying \(MV_0V_1\), with bounded-coefficient remainder controlled by (3). For \(1<s<2\),
\[
 f_{1/2}(s)=\sqrt{\frac{\mathrm e^\gamma}{\pi s}}
      \int_1^s\frac{dt}{\sqrt{t(t-1)}},\qquad
 F_{1/2}(s)=2\sqrt{\frac{\mathrm e^\gamma}{\pi s}}.
\]
Only the lower bound is needed. Here \(s=\log D/\log z=(2+\eta)(1/2-\eta/16)\), so \(1+\eta/3<s<1+\eta/2\). In particular \(f_{1/2}(s)\ge c_0\sqrt\eta\), with absolute \(c_0>0\). For sufficiently large \(X\) depending on the fixed \(\eta\), the number \(S\) of primes surviving through \(z\) therefore satisfies
\[
 S\ge c_1\sqrt\eta\,
 \frac{X}{(\log X)^{3/2}\log y}
\tag{4}
\]
with absolute \(c_1>0\). Indeed \(M\asymp X/\log X\) and the product \(V_0V_1\asymp1/(\sqrt{\log X}\log y)\).

## 4. Switching the two remaining inert factors

If \(N\) counted in (4) has any inert factors, their total multiplicity is even since \(N\equiv1\bmod4\). Each is at least \(z\) and \(z^4>8X+1\), so there are exactly two, counted with multiplicity. Write
\[
 N=kqr,\quad z\le q\le r,\qquad
 k\le B=(8X+1)/z^2,\qquad q\le\sqrt{(8X+1)/k},
\]
where \(q,r\) are inert primes and all primes dividing \(k\) are \(1\bmod4\). This includes \(k=1\) and \(q=r\).

For fixed \(k,q\) put \(H=kq,\ Y=(8X+1)/H\). Discard pairs with \(Y<z\). To upper-bound the count of eligible \(r\le Y\), start with all integers up to \(Y\). Set \(D'=Y^{1/20}\), \(b=(D')^{1/20}\), so \(y<b<z\) for sufficiently large \(X\). For each prime \(5\le\ell\le b\), exclude 0 as a possible class of \(r\). If \(\ell\nmid H\), also exclude \(H^{-1}\), since \(p=(Hr-1)/4>X\) is prime. For \(\ell\le y\) with \(\ell\nmid H\), further exclude \(3H^{-1}\), since \(n=(Hr-3)/2\) has no small prime factor. These roots are distinct for \(\ell\ge5\). If \(\ell\mid H\) only 0 is excluded. In particular \(q=r\) causes no invalid exclusion, since \(q\ge z>b\). Let \(v(\ell)\) be the number of excluded classes (between 1 and 3), extended multiplicatively to squarefree integers. For a squarefree product \(m\) of the sieving primes, all its excluded local conditions together hold for \(Yv(m)/m+O(v(m))\) integers, with an absolute error constant.

Use Selberg's upper-bound sieve at truncation \(D'\). In its elementary quadratic-form version the bound is
\[
\frac{Y}{G}+
 O\left(\sum_{\substack{m\le (D')^2\\m\ {\rm squarefree}}}3^{\omega(m)}v(m)\right),\qquad
G=\sum_{\substack{d\le D'\\d\mid\prod_{5\le\ell\le b}\ell}}
      \prod_{\ell\mid d}\frac{v(\ell)}{\ell-v(\ell)} .
\]
Here the condition on \(d\) means every prime divisor is in \([5,b]\). The error follows from \(|\lambda_d|\le1\) for the optimal Selberg weights and the \(3^{\omega(m)}\) ordered pairs of squarefree divisors with least common multiple \(m\), before truncation. Since \(v(m)\le3^{\omega(m)}\), it is \(O(Y^{1/10}(1+\log Y)^8)\) by the elementary nine-fold divisor bound.

In the full Euler product for \(G\) before restricting \(d\le D'\), a prime \(\ell\) is independently present with probability \(v(\ell)/\ell\), after normalization. Its expected contribution to \(\log d\), summed over all \(\ell\), is at most
\(3\sum_{\ell\le b}\log\ell/\ell\le4\log b<\tfrac12\log D'\) for large \(X\). Markov's inequality thus shows that truncation preserves at least half the mass. Comparing the local factors with \(1-2/\ell\) for \(y<\ell\le b\) and \(1-3/\ell\) for \(5\le\ell\le y\), Mertens' estimates give
\[
G^{-1}\ll\frac{H^*(H)}{(\log Y)^2\log y},\qquad
H^*(h)=\prod_{\substack{\ell\mid h\\\ell\ge5}}(1+10/\ell).
\tag{5}
\]
Indeed the survival-factor ratio at a prime dividing \(H\) is at most \((1-1/\ell)/(1-3/\ell)\le1+10/\ell\). At the other primes, comparison with \((1-1/\ell)^2\) or \((1-1/\ell)^3\) has a bounded product of corrections, as the local ratios are \(1+O(\ell^{-2})\). The factors 2 and 3 cause only absolute constants. Since \(\log b=(\log Y)/400\) and \(Y\ge z\), also \(\log Y\asymp\log X\) uniformly.

To sum (5), \(H^*(kq)\le H^*(k)H^*(q)\) and \(H^*(q)\ll1\). The two harmonic sums obey
\[
\begin{aligned}
\sum_{\substack{k\le B\\\ell\mid k\Rightarrow\ell\equiv1\bmod4}}\frac{H^*(k)}k
 &\le\prod_{\substack{\ell\le B\\\ell\equiv1\bmod4}}
       \left(1+\frac{1+10/\ell}{\ell-1}\right)
 \ll\sqrt{\log(2B)}\ll\sqrt{\eta\log X},\\
\sum_{z\le q\le\sqrt{8X+1}}\frac1q
 &\le\log((2+\eta)/2)+o(1)\ll\eta .
\end{aligned}
\]
The second sum is over all primes, an admissible enlargement. The bounds use Mertens' estimates and \(\log B=\eta\log X/(2+\eta)+O(1)\). The constants are absolute, with \(X\) sufficiently large depending on \(\eta\). The sum of the Selberg remainder terms is negligible. Indeed each is \(O(Yz^{-9/10}(1+\log X)^8)\), and \(\sum_{k,q}Y\ll X(1+\log X)^2\) even when the primality restrictions are dropped. The total number lost after (4) is thus at most
\[
C_1\eta^{3/2}\frac{X}{(\log X)^{3/2}\log y}
       +O\bigl(Xz^{-9/10}(1+\log X)^{10}\bigr)
\tag{6}
\]
with absolute \(C_1\). The extra \((\log y)^{-1}\) comes from the third root \(3H^{-1}\) for small primes. Retaining this factor is necessary for the comparison with (4).

## 5. Conclusion and sources

Choose \(\eta>0\) sufficiently small that \(C_1\eta<c_1/2\), and then take \(X\) sufficiently large. Subtracting (6) from (4) leaves \(\gg X/((\log X)^{3/2}\log y)\) primes \(p\) satisfying both restrictions in Section 1. The map \(p\mapsto n=2p-1\) is injective. By (1) the representable values form a lower-order subset. Take \(X=T/4\), and use \(\log y=4\log\log X\). This proves the theorem.

- Petersen, Validashti and Wayland, the source triangle problem. [Published paper](https://doi.org/10.1080/0025570X.2026.2627861) and [OEIS A400795](https://oeis.org/A400795).
- H. Iwaniec, *Primes represented by quadratic polynomials in two variables*, Acta Arith. 24 (1974), 435–459, in particular the semilinear sieve and switching in the proof of Lemma 14. [Article](https://matwbn.icm.edu.pl/ksiazki/aa/aa24/aa2451.pdf).
- K. Matomäki, *The binary Goldbach problem with one prime of the form \(p=k^2+l^2+1\)*, J. Number Theory 128 (2008), 1195–1210. Section 2, Lemma 2 gives the half-dimensional sieve inequalities and explicit functions. Sections 5–6 illustrate the lower sieve and the switched upper estimate. [Author's copy](https://users.utu.fi/ksmato/wp-content/uploads/sites/1432/2025/04/Goldbach_k2pl2p1.pdf).
- G. Oh, *Applications of the Selberg sieve*, Theorem 1.1 gives the arbitrary-prime-product Selberg upper bound and its optimal weights used in Section 4. [Lecture notes](https://web.math.princeton.edu/~gyujino/Selbergsieve.pdf).
- K. Nath and L. Xie, *Almost primes and primes that are sums of two squares plus 1*, Lemmas 3.2 and 3.6 and the beginning of Section 5 give the weighted Bombieri–Vinogradov estimate and a further formulation of the half-dimensional sieve functions. Their main theorem concerns \(p-1\) and \(p+2\). The Bonferroni presieve and the third small switched root above establish the needed simultaneous restrictions for \(4p+1\) and \(2p-1\). [arXiv:2501.16723](https://arxiv.org/abs/2501.16723).

Codex prepared this manuscript for @dwilfand-sys. It addresses the conjecture on paper. External expert review, a Lean certificate and historical priority remain unconfirmed.

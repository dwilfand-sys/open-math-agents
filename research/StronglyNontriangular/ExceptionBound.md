# A quantitative upper bound for the strongly nontriangular numbers

Let \(P(a,b)=(ab+a+b-\gcd(a,b))/2\) and let \(R(n)\) count its coprime representations with an even coordinate one less than a prime and the other coordinate odd, both greater than one.

**Theorem.** There exist absolute constants \(c_1,c_2,C>0\) such that, for all sufficiently large \(X\),
\[
\#\{1\le n\le X:R(n)<c_1\sqrt{\log\log X}\}
 \le CX\exp(-c_2\sqrt{\log\log X}).
\]
This also bounds the number of terms of [A400795](https://oeis.org/A400795) at most \(X\).

The triangle problem is due to [Petersen, Validashti and Wayland](https://doi.org/10.1080/0025570X.2026.2627861). [Erdős and Pomerance, Theorem 4.1 and (4.2)–(4.4)](https://renyi.hu/~p_erdos/1986-11.pdf), analyze the sum of the logarithms of the same gcds over the prime factors of \(N=2(n+1)\). The proof below counts the primes at which the gcd is one, following the connection to coprime lattice-point representations. Its analytic inputs are Mertens' estimates and the [Siegel–Walfisz and Brun–Titchmarsh theorems](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/BrunTitchmarsh.pdf).

### 1. A set of potential prime witnesses

Assume \(X\) is an integer and put
\[
L=\log\log X,\quad K=\exp(\sqrt L),\quad J=2\lceil10\sqrt L\rceil,\quad
Y=X^{1/(10J)},\quad T=\exp(\sqrt{\log X}).
\]
For large \(X\) we have \(2<K<T<Y\). Let \(A(t)\) count odd primes \(q\le t\) for which \(q-1\) has no odd prime divisor \(s\le K\). Uniformly on \(T\le t\le Y\),
\[
A(t)\gg\frac{t}{\sqrt L\log t}.
\]
Here is the truncation argument. The formal local proportion is
\[
V(K)=\prod_{3\le s\le K,\ s\ {\rm prime}}(1-1/(s-1))\asymp1/\log K=1/\sqrt L.
\]
Indeed \((1-1/(s-1))/(1-1/s)=1-1/(s-1)^2\), whose product over odd primes converges positively, and Mertens' product theorem applies. Also \(\sigma=\sum_{3\le s\le K,\ s\ {\rm prime}}1/(s-1)=\tfrac12\log L+O(1)\).

Take the least odd \(m\ge10\log L\). The odd Bonferroni sum through degree \(m\) is a lower bound for \(A(t)\), up to deletion of the prime \(2\). For each squarefree product \(d\) of at most \(m\) distinct odd primes up to \(K\), it involves the count \(\pi(t;d,1)\). Uniformly,
\[
d\le K^m=\exp(O(\sqrt L\log L))\le\log t.
\]
Siegel–Walfisz gives \(\pi(t;d,1)=\operatorname{Li}(t)/\varphi(d)+O(t\exp(-c\sqrt{\log t}))\). There are at most \(K^m\le\log t\) distinct moduli in this sum, so their total error is \(o(t/(\sqrt L\log t))\), uniformly on \(T\le t\le Y\). The truncated sum of main terms differs from \(\operatorname{Li}(t)V(K)\) by at most \(\operatorname{Li}(t)\sigma^{m+1}/(m+1)!\), by applying the next Bonferroni bound to independent events of probabilities \(1/(s-1)\). The factorial estimate bounds this relative-to-\(\operatorname{Li}(t)\) error by \(O(L^{-5})\). This proves the stated lower bound.

Partial summation, keeping just the integral from \(T\) to \(Y\), now yields
\[
\sum_{\substack{q\le Y\\q\ {\rm counted\ by}\ A}}1/q
\gg\frac{\log\log Y-\log\log T}{\sqrt L}\gg\sqrt L.
\]
In fact \(\log\log T=L/2\) and \(\log\log Y=L-\log(10J)\). Fix an absolute \(0<b<1/2\) small enough and choose a subset \(Q\) of these primes whose reciprocal sum \(\lambda\) lies in \([b\sqrt L,b\sqrt L+1]\). This can be done by adding primes until the lower threshold is crossed.

### 2. Most integers have many candidate divisors

For \(n\) uniform up to \(X\), let \(D=\#\{q\in Q:q\mid n+1\}\). We bound \(\mathbb E_X 2^{-D}\) by comparing it to the independent model, where the answer is \(\prod_{q\in Q}(1-1/(2q))\le e^{-\lambda/2}\).

For an actual \(n\), expand \(\prod_{q\in Q}(1-\tfrac12{\bf1}_{q\mid n+1})\) by the upper Bonferroni sum through even degree \(J\). This inequality follows, for example, by applying ordinary Bonferroni to independent auxiliary coin flips on the primes dividing \(n+1\). Counting the joint congruences in \(n\), each subset of distinct primes with product \(u\) has mean indicator \(1/u+O(1/X)\). Summing the rounding errors costs at most \(O((J+1)Y^J/X)\). By the next Bonferroni bound, the even sum in the independent model exceeds the exact product by at most \((\lambda/2)^{J+1}/(J+1)!\). Therefore
\[
\mathbb E_X 2^{-D}\le e^{-\lambda/2}
+\frac{(\lambda/2)^{J+1}}{(J+1)!}
+O((J+1)X^{-9/10}).
\]
Since \(J\ge20\sqrt L\) and \(\lambda\le\sqrt L\) for large \(X\), the second term is \(O(e^{-2\lambda})\) by the factorial bound. The last term is smaller. Markov's inequality consequently gives
\[
\Pr(D<\lambda/2)\le 2^{\lambda/2}\mathbb E_X 2^{-D}
\ll\exp(-\tfrac12(1-\log 2)\lambda).
\]

### 3. Few of these divisors are spoiled

For \(q\in Q\) the remaining possible odd common factors of \(q-1\) and \(2n+1\) exceed \(K\). Put \(H_K(q)=\sum_{s\mid q-1,\ s>K,\ s\ {\rm prime}}1/s\). The elementary consequence of Brun–Titchmarsh we need, uniformly here, is
\[
\sum_{\substack{q\le Y\\q\ {\rm prime}}}H_K(q)/q\ll (1+\log\log Y)/K.
\]
For \(q\le K^4\) at most four prime divisors of \(q-1\) exceed \(K\), giving a contribution \(O((1+\log\log K)/K)\). For \(t\ge K^4\), sum over primes \(q\le t\), splitting the offending primes \(s\) at \(t^{1/4}\). For \(K<s\le t^{1/4}\), the prime class \(q\equiv1\bmod s\) contains at most \(4t/((s-1)\log t)\) members. Larger \(s\) contribute at most \(4t^{-1/4}\) per \(q\). Hence
\[
\sum_{q\le t,\ q\ {\rm prime}} H_K(q)\ll t/(K\log t)+t^{3/4},
\]
using \(\sum_{m>K}1/(m(m-1))\ll1/K\). Partial summation on \([K^4,Y]\) gives the bound, since \(\int_{K^4}^\infty t^{-5/4}\,dt=4/K\).

Let \(B\) count the primes dividing \(n+1\) in \(Q\) for which \(\gcd(q-1,2n+1)>1\). For every individual offending \(s\), the events \(q\mid n+1\) and \(s\mid2n+1\) have joint frequency \(1/(qs)+O(1/X)\). The union bound, with at most \(Y^2\) pairs, gives
\[
\mathbb E_X B\ll L/K+Y^2/X,\qquad
\Pr(B>\lambda/4)\ll\sqrt L\exp(-\sqrt L)+Y^2/(X\lambda).
\]

On \(D\ge\lambda/2,\ B\le\lambda/4\), each of the \(D-B\) unspoiled primes gives a distinct pair \(a=q-1\) even and \(b=2(n+1)/q-1\) odd, apart from the single possible \(q=n+1\). Indeed \(\gcd(a,b)=\gcd(q-1,2n+1)=1\) and then \(P(a,b)=n\). Thus \(R(n)\ge\lambda/4-1\), and the two probability bounds give the theorem.

The constants are existential. The bound concerns the frequency of exceptions and leaves their infinitude undetermined. No formal kernel verdict or priority determination is claimed.

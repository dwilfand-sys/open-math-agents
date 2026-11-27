# Coprime triangle representations from products of \(k\) primes

Fix an integer \(k\ge1\). For the [A400795](https://oeis.org/A400795) triangle-count function \(P(a,b)=(ab+a+b-\gcd(a,b))/2\), let \(R_k(n)\) count its unordered coprime representations with \(a>1\) even, \(b>1\) odd, and \(a+1\) a product of exactly \(k\) **distinct** odd primes. Set
\[
C(n)=\prod_{\substack{s\mid2n+1\\s\ {\rm prime}}}(1-1/(s-1)),
\qquad L=\log\log X.
\]

**Theorem.** For \(n\) uniform on \(1,\ldots,X\),
\[
\mathbb E_X\left|\frac{k!R_k(n)}{L^k}-C(n)\right|\longrightarrow0.
\]
In particular the mean of \(R_k\) is asymptotic to \(2A L^k/k!\), with \(A\) Artin's constant. For every fixed \(d>0\), the proportion of \(n\le X\) having at least \((\log\log X)^d\) unordered coprime representations of the unrestricted form \(P(a,b)\) tends to one.

The motivating triangle problem is due to [Petersen, Validashti and Wayland](https://doi.org/10.1080/0025570X.2026.2627861). An earlier normal-order analysis by Erdős and Pomerance [“On the Number of False Witnesses for a Composite Number,” *Mathematics of Computation* 46 (1986), 259–279, Theorem 4.1 and (4.2)–(4.4)](https://renyi.hu/~p_erdos/1986-11.pdf) treats the sum of \(\log\gcd(q-1,N-1)\) over prime factors \(q\mid N\). At \(N=2(n+1)\) this is precisely the shifted gcd used for the prime case below. They truncate common divisors and estimate the distributions of the prime factors in progressions. Here we count exact coprimality for products of \(k\) distinct prime divisors and interpret it as a triangle representation.

### Divisors and truncations

For each odd \(u>1\) dividing \(n+1\), take \(a=u-1\) and \(b=2(n+1)/u-1\). Then \(b\equiv2n+1\bmod(u-1)\). Thus each divisor \(u<n+1\) with \(\gcd(u-1,2n+1)=1\) yields a coprime representation, and each representation in the definition of \(R_k\) has exactly this form. Parity distinguishes the coordinates.

Write \(Y=X^{1/(4k)}\), take \(K\ge3\) fixed, and let \(W\) be the product of odd primes at most \(K\). Approximate \(R_k\) by \(D_{K,k}\), the number of products \(u\) of \(k\) distinct primes \(K<q_i\le Y\) that divide \(n+1\) and satisfy \(\gcd(u-1,2n+1,W)=1\). The latter condition excludes exactly the common prime factors at most \(K\).

The number of prime factors of \(n+1\) exceeding \(Y\) is at most \(4k+1\) for large \(X\), while at most \(K\) prime factors are at most \(K\). If \(Z=\omega(n+1)\) counts distinct prime factors, the number of \(k\)-fold products containing an omitted prime is at most \((K+4k+1)(1+Z)^{k-1}\). The forbidden divisor \(u=n+1\) accounts for at most one more discrepancy.

We record that \(\mathbb E_X(1+Z)^{2k}\ll_k(1+L)^{2k}\). To see this, the contribution to \(Z\) from primes above \(Y\) is bounded as just observed. For any \(j\le2k\), expand the \(j\)-th power of the count of divisors \(q\le Y\), \(q\) prime. For an ordered tuple with \(l\) distinct primes, the expectation of its indicator is the reciprocal of their product plus \(O(1/X)\). Summing over equality patterns bounds the contribution by \(O_k((1+\sum_{q\le Y}1/q)^j+Y^j/X)\), as asserted. Consequently omitted-prime products have mean \(O_{K,k}((1+L)^{k-1})\).

### Products in reduced residue classes

Condition on \(n\equiv r\bmod W\). For each unit class \(c\bmod W\), let \(N_c(n)\) count the prime factors \(K<q\le Y\) of \(n+1\) congruent to \(c\bmod W\). The prime number theorem for fixed progressions and partial summation give
\[
\sum_{\substack{K<q\le Y\\q\ {\rm prime},\ q\equiv c\bmod W}}1/q
=(1/\varphi(W)+o_{K,k}(1))L.
\]
Conditional probabilities of divisibility by \(q\) and by distinct \(qq'\) differ from \(1/q\) and \(1/(qq')\) by \(O(W/X)\). The second-moment comparison with independent Bernoulli variables of parameters \(1/q\) thus shows that \(N_c/L\to1/\varphi(W)\) in probability. There are finitely many classes for fixed \(K\), so this holds jointly.

Ordered \(k\)-tuples can first be counted with repetition, using products of the \(N_c\); deleting repeated primes costs \(O_k((1+Z)^{k-1})\) tuples. A product of \(k\) independently uniform units mod \(W\) is uniform on its unit group. The proportion of residues \(u\) satisfying \(\gcd(u-1,2r+1,W)=1\) is
\[
C_K(r)=\prod_{\substack{s\mid\gcd(W,2r+1)\\s\ {\rm prime}}}(1-1/(s-1)),
\]
by the Chinese remainder theorem. Therefore \(k!D_{K,k}/L^k-C_K(n)\to0\) in probability, first in each class and then overall. The moment bound for \(Z\) gives a uniform second-moment bound for \(D_{K,k}/L^k\) because \(D_{K,k}\le(1+Z)^k\). Convergence also holds in mean absolute value.

### Obstructions from large primes

For \(u>1\) put \(H_K(u)=\sum_{s\mid u-1,\ s>K,\ s\ {\rm prime}}1/s\). Each erroneous inclusion in \(D_{K,k}\) requires \(u\mid n+1\) and \(s\mid2n+1\) for at least one such \(s\). Since \(s\nmid u\), this pair of conditions has frequency \(1/(us)+O(1/X)\). All possible \(u\) and \(s\) are at most \(Y^k\), giving total rounding error \(O(Y^{2k}/X)=o(1)\). We must bound
\[
\sum_{K<q_1<\cdots<q_k\le Y}\frac{H_K(q_1\cdots q_k)}{q_1\cdots q_k},
\]
with all \(q_i\) prime.

Fix the first \(k-1\) primes, let \(v\) be their product, and take \(z=q_{k-1}\) (for \(k=1\), take \(v=1,z=2\)). For \(t\ge z\) and primes \(z<q\le t\), one has \(vq\le t^k\). A possible divisor \(s>K\) of \(vq-1\) is coprime to \(v\). For \(s\le t^{1/4}\), the condition \(vq\equiv1\bmod s\) puts \(q\) in one reduced prime progression; [Brun–Titchmarsh](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/BrunTitchmarsh.pdf) bounds its count by \(4t/((s-1)\log t)\). There are at most \(4k\) prime divisors of \(vq-1\) exceeding \(t^{1/4}\). Consequently
\[
\sum_{\substack{z<q\le t\\q\ {\rm prime}}}H_K(vq)
\le 4t/(K\log t)+4k\,t^{-1/4}\pi(t).
\]
Partial summation from \(z\) to \(Y\), using the convergence of \(\int_2^\infty t^{-5/4}\,dt\), gives
\[
\sum_{\substack{z<q\le Y\\q\ {\rm prime}}}\frac{H_K(vq)}q
\ll (1+\log\log Y)/K+O_k(1),
\]
uniformly in the earlier primes. Summing their reciprocal products contributes \(O_k((1+L)^{k-1})\). Hence the mean number of inclusions spoiled by primes larger than \(K\) is \(O_k(L^k/K+(1+L)^{k-1})\), with the first constant independent of \(K\).

Finally \(0\le C_K(n)-C(n)\le\sum_{s\mid2n+1,\ s>K}1/(s-1)\), with the sum over primes. Its mean is at most \(1/K+O(\log X/X)\), by counting \(n\) in one reduced class mod each odd \(s\). Combining the estimates, taking \(X\to\infty\) first, then \(K\to\infty\), proves the theorem.

### Mean and multiplicity

CRT gives the limiting law of the bounded product \(C_K(n)\) as the product of independent factors indexed by the odd primes \(s\le K\), each equal to \(1-1/(s-1)\) with probability \(1/s\), and to \(1\) otherwise. The tail estimate gives convergence to the analogous infinite product. This random limit is strictly positive almost surely because \(\sum_s (1/s)(-\log(1-1/(s-1)))<\infty\). Its mean is \(\prod_{s\ge3,\ s\ {\rm prime}}(1-1/(s(s-1)))=2A\). This proves the mean assertion. For a prescribed real \(d>0\), choose any integer \(k>d\). Since the limiting law of \(k!R_k/L^k\) gives zero probability to zero and \(k!L^{d-k}\to0\), \(R_k\ge L^d\) holds with probability tending to one. The full count is at least \(R_k\).

This argument proves lower multiplicity and the asymptotics for each fixed \(k\). Infinitude of the strongly nontriangular exceptions and historical priority remain undetermined.

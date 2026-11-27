# How many coprime triangle representations does a typical integer have?

This note refines the density theorem for [OEIS A400795](https://oeis.org/A400795). Let \(R(n)\) count the unordered representations
\[
n=P(a,b)=(ab+a+b-\gcd(a,b))/2,\qquad a,b>1,\quad \gcd(a,b)=1,
\]
whose even coordinate is one less than an odd prime and whose other coordinate is odd. Define
\[
C(n)=\prod_{\substack{s\mid 2n+1\\s\ \mathrm{prime}}}
 \left(1-\frac1{s-1}\right).
\]

**Theorem.** With all logarithms natural,
\[
\frac1X\sum_{3\le n\le X}
\left|\frac{R(n)}{\log\log n}-C(n)\right|\longrightarrow0.
\]
The mean of \(R(n)\) on \(1\le n\le X\) is asymptotic to \(2A\log\log X\), where \(A=\prod_{p\ {\rm prime}}(1-1/(p(p-1)))\) is Artin's constant. For every positive function \(f(n)=o(\log\log n)\), the set with \(R(n)\ge f(n)\) has density one.

The closest predecessor we located is Paul Erdős and Carl Pomerance, [“On the Number of False Witnesses for a Composite Number,” *Mathematics of Computation* 46 (1986), 259–279, Theorem 4.1 and (4.2)–(4.4)](https://renyi.hu/~p_erdos/1986-11.pdf). They give a normal-order formula for \(\log F(N)=\sum_{q\mid N,\ q\ {\rm prime}}\log\gcd(q-1,N-1)\). At \(N=2(n+1)\) their gcd is exactly the one used here. Their proof truncates the common divisors and estimates counts of prime divisors in arithmetic progressions, drawing on Norton's work. Our argument develops these related ideas for the indicator \({\bf1}_{\gcd(q-1,N-1)=1}\) and its application to the triangle problem of [Petersen, Validashti and Wayland](https://doi.org/10.1080/0025570X.2026.2627861). The multiplicative factor \(C(n)\) reflects counting the zero-log terms of their sum.

### The witness and its small prime obstructions

The identity \((a+1)(b+1)=2(n+1)\) shows that \(R(n)\) equals the number of odd primes \(q\mid n+1\) for which \(q<n+1\) and \(\gcd(q-1,2n+1)=1\). Indeed, the even coordinate \(a=q-1\) determines the odd coordinate \(b=2(n+1)/q-1\), and \(b\equiv2n+1\bmod(q-1)\).

Take \(X\) integral, \(Y=X^{1/8}\), \(L=\log\log X\), and let \(\mathbb E_X\) be the uniform mean on \(1\le n\le X\). Fix \(K\ge3\) and let \(W\) be the product of odd primes at most \(K\). Write \(C_K(n)\) for the product defining \(C(n)\) restricted to \(s\le K\). In a fixed residue class \(n\equiv r\bmod W\), let \(D_K(n)\) count primes \(K<q\le Y\) dividing \(n+1\) for which \(q\not\equiv1\bmod s\) whenever \(s\mid\gcd(2r+1,W)\).

By the Chinese remainder theorem, the number of allowed reduced classes \(q\bmod W\) is \(\varphi(W)C_K(r)\). For each prime \(s\mid\gcd(2r+1,W)\), just one of the \(s-1\) units is forbidden. The prime number theorem in each fixed progression, followed by partial summation, gives
\[
\lambda_r:=\sum_{\substack{K<q\le Y\\q\ {\rm allowed\ prime}}}1/q
=C_K(r)L+o_K(L).
\]
Here \(\log\log Y=L+O(1)\). Conditional on \(n\equiv r\bmod W\), the chance of \(q\mid n+1\) is \(1/q+O(W/X)\), and for distinct \(q,q'\) the corresponding joint chance is \(1/(qq')+O(W/X)\), by counting integers in a residue class. Comparing with independent Bernoulli variables of means \(1/q\) thus bounds the conditional second moment of \(D_K-\lambda_r\) by \(\lambda_r+O(WY^2/X)\). (There are at most \(Y\) indices and every term of the expanded second moment incurs an error \(O(W/X)\).) Cauchy–Schwarz and averaging over the finitely many classes give
\[
\mathbb E_X|D_K/L-C_K(n)|\longrightarrow0
\qquad(K\ {\rm fixed}).
\]

### Average contribution from larger obstructions

Put \(H_K(q)=\sum_{s\mid q-1,\ s>K,\ s\ {\rm prime}}1/s\). For \(s\le t^{1/4}\), the [Brun–Titchmarsh inequality](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/BrunTitchmarsh.pdf) bounds the number of primes \(q\le t\), \(q\equiv1\bmod s\), by \(4t/((s-1)\log t)\). For each \(q\le t\), at most four distinct primes \(s>t^{1/4}\) can divide \(q-1\). Using \(\sum_{m>K}1/(m(m-1))=1/K\), we obtain
\[
\sum_{q\le t,\ q\ {\rm prime}}H_K(q)
\le \frac{4t}{K\log t}+4t^{-1/4}\pi(t).
\]
Partial summation gives
\[
\limsup_{Y\to\infty}\frac1{\log\log Y}
\sum_{q\le Y,\ q\ {\rm prime}}\frac{H_K(q)}q\le4/K.
\]

An integer \(n+1\le X+1\) has at most nine distinct prime divisors exceeding \(Y\) for all sufficiently large \(X\). Discarding \(q\le K\), these large primes, and the possible \(q=n+1\) changes the witness count by \(O_K(1)\). Each remaining discrepancy between \(R(n)\) and \(D_K(n)\) requires \(q\mid n+1,\ s\mid q-1,\ s\mid2n+1\) for some prime \(s>K\). The congruences in \(n\) have joint frequency \(1/(qs)+O(1/X)\), as \(s\ne q\) and \(s\) is odd. The number of pairs indexed here is at most \(Y^2\). It follows that
\[
\limsup_{X\to\infty}\mathbb E_X|D_K-R|/L\le4/K.
\]
Finally \(0\le C_K(n)-C(n)\le\sum_{s\mid2n+1,\ s>K}1/(s-1)\), and its mean is at most
\[
\sum_{K<s\le2X+1,\ s\ {\rm prime}}\frac1{s-1}
\left(\frac1s+O(1/X)\right)\le\frac1K+O(\log X/X).
\]
The triangle inequality and \(K\to\infty\) prove \(\mathbb E_X|R/L-C(n)|\to0\). On \(\sqrt X\le n\le X\), \(\log\log n=L+O(1)\) uniformly, and \(\mathbb E_X(R/L)\) stays bounded by the result just proved. The contribution from \(3\le n<\sqrt X\) vanishes since \(R(n)\le\log(n+1)/\log2\). This proves the displayed theorem with denominator \(\log\log n\).

### Limiting distribution and mean

Let \(U_s\) be independent Bernoulli variables with \(\Pr(U_s=1)=1/s\), indexed by odd primes. For fixed \(K\), the Chinese remainder theorem identifies the limiting distribution of \(C_K(n)\) with the finite product \(\prod_{3\le s\le K}(1-1/(s-1))^{U_s}\). The corresponding infinite random product \(C_\infty\) converges to a strictly positive number almost surely, since \(\sum_s\mathbb E[U_s/(s-1)]<\infty\) and \(-\log(1-1/(s-1))\le2/(s-1)\). The finite random products approximate the infinite one in mean by the same tail sum. Together with the arithmetic tail estimate above, finite approximation against bounded Lipschitz test functions shows that both \(C(n)\) and \(R(n)/L\), with \(n\) uniform up to \(X\), converge in distribution to \(C_\infty\).

Independence gives \(\mathbb E C_\infty=\prod_{s\ge3,\ s\ {\rm prime}}(1-1/(s(s-1)))=2A\). Since \(C(n)\in[0,1]\), the mean of \(C(n)\) tends to \(2A\), hence the mean of \(R(n)/L\) has the same limit. Finally \(C_\infty>0\) almost surely, so the limiting upper probability of \(R(n)/L\le\varepsilon\) tends to zero as \(\varepsilon\downarrow0\). For \(f(n)=o(\log\log n)\), one has \(f(n)\le\varepsilon L\) for all sufficiently large \(n\le X\). This yields the claimed density-one multiplicity.

The mean constant counts the prime-witness subfamily defined above. The full triangle count may be larger. All claims in this note are analytic derivations without a Lean kernel verdict.

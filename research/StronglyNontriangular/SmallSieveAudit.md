# Progression estimate after removing the small prime obstructions

This lemma supplies the input to the semilinear sieve in the proposed infinitude proof for [A400795](https://oeis.org/A400795). It keeps the forms \(2p-1\) and \(4p+1\) in the small sieve simultaneously. Let \(0<\delta<1/8\) be fixed, \(y=(\log X)^4\), and \(D=X^{1/2-\delta}\). Let \(\mathcal B\) consist of the integers \(4p+1\) with \(X<p\le2X\) prime, \(p\equiv1\bmod3\), such that

* \(2p-1\) has no prime divisor at most \(y\), and
* \(4p+1\) has no prime divisor \(s\le y\) with \(s\equiv3\bmod4\).

The primes 2 and 3 are automatically harmless. For \(5\le s\le y\) prime let \(\nu(s)=1+{\bf1}_{s\equiv3\bmod4}\); the forbidden residues are \(1/2\bmod s\) and, when relevant, \(-1/4\bmod s\), distinct nonzero classes. Put
\[
M=(\operatorname{Li}(2X)-\operatorname{Li}(X))/2,\qquad
V=\prod_{5\le s\le y,\ s\ {\rm prime}}(1-\nu(s)/(s-1)).
\]
Let \(d\) range over squarefree integers whose prime factors are \(>y\) and \(3\bmod4\), including \(d=1\). Then for each fixed \(A>0\),
\[
\sum_{d<D}
\left|\#\{b\in\mathcal B:d\mid b\}
 - M V/\varphi(d)\right|\ll_{A,\delta} X/(\log X)^A .
\]

**Proof.** Let \(m\) be the least even integer at least \(2\log\log X\). Put \(h(s)=\nu(s)/(s-1)\). Bonferroni through adjacent degrees \(m,m+1\) bounds the exact indicator of absence of the small bad classes above and below. Each modulus \(e\) in these sums is the product of at most \(m+1\) primes at most \(y\), so \(e\le y^{m+1}=\exp(O((\log\log X)^2))=X^{o(1)}\). For each given \(e,d\), the CRT yields \(\nu(e)=\prod_{s\mid e}\nu(s)\) reduced classes modulo \(3de\). The conditions include \(p\equiv1\bmod3\) and \(p\equiv-1/4\bmod d\). Substituting prime main terms gives \(M/\varphi(d)\) times the appropriate truncation of \(\prod_{s\le y}(1-h(s))\).

The upper and lower main terms differ by at most
\[
\frac M{\varphi(d)}\frac{\sigma^{m+1}}{(m+1)!},\qquad
\sigma=\sum_{5\le s\le y}h(s)\ll\log\log y.
\]
Here and below a sum over \(s\) uses primes. Since \(\log\log y=O(\log\log\log X)\), the factorial quotient is \(O_B((\log X)^{-B})\) for every fixed \(B\). Also \(\sum_{d<D}1/\varphi(d)\le\prod_{p\le D}(1+1/(p-1))\ll\log X\) for these squarefree \(d\). The exact \(V\) lies between the two main-term truncations by applying Bonferroni to independent events with probabilities \(h(s)\).

It remains to bound the sum of errors in counting primes. For \(j\le X^{1/2-\delta/2}\), denote by \(E(j)\) the maximum over reduced classes \(a\bmod j\) of the absolute discrepancy between the count of primes in \((X,2X]\) and \((\operatorname{Li}(2X)-\operatorname{Li}(X))/\varphi(j)\). All moduli \(j=3de\) fall in this range for large \(X\). For a fixed \(j\), \(d,e\) are unique by the disjoint prime ranges and \(\nu(e)\le2^{\omega(j)}\). Adding the errors from both truncations is at most \(2\sum_{j\le X^{1/2-\delta/2}}2^{\omega(j)}E(j)\).

The Bombieri–Vinogradov theorem gives \(\sum E(j)\ll_B X/(\log X)^B\) for arbitrary fixed \(B\). The trivial bound \(E(j)\ll X/j+X/(\varphi(j)\log X)+1\ll X\tau(j)/j\) in this range and the elementary divisor moment estimate \(\sum_{j\le X}\tau(j)^3/j\ll(\log X)^{O(1)}\) give \(\sum4^{\omega(j)}E(j)\ll X(\log X)^{O(1)}\). Cauchy–Schwarz with the measure \(E(j)\) proves the required divisor-weighted bound on the error. Combining both parts establishes the claimed estimate.

The moving set of sieving primes \(s>y,\ s\equiv3\bmod4\) with local probability \(1/(s-1)\) satisfies the usual half-dimensional upper-product condition with an absolute constant: omit factors from the ordinary \(3\bmod4\) Mertens product when the interval begins below \(y\). Therefore the standard semilinear lower sieve applies directly to \(\mathcal B\), with scale \(MV\), distribution level \(D\) and total remainder as shown above. [Matomäki, Lemma 2, including the explicit lower semilinear function](https://users.utu.fi/ksmato/wp-content/uploads/sites/1432/2025/04/Goldbach_k2pl2p1.pdf).

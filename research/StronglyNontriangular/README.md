# Density of strongly nontriangular numbers

Kyle Petersen's [OEIS A400795](https://oeis.org/A400795) asks whether the positive integers outside
\[
\{1\}\ \cup\ \left\{P(a,b)=\frac{ab+a+b-\gcd(a,b)}2:\ a,b\in\mathbb Z,\ a,b>1\right\}
\]
are infinite and have natural density zero. These are two distinct questions. Petersen, Validashti and Wayland studied these lattice-point counts and proved infinitude of the integers missing from the restricted image with coprime inputs. Their [published abstract](https://doi.org/10.1080/0025570X.2026.2627861) describes infinitude for unrestricted inputs as a conjecture.

**Theorem.** For every fixed positive integer \(h\), the set of \(n\) having at least \(h\) distinct unordered representations \(n=P(a,b)\) by coprime integers \(a,b>1\) has natural density one. Each representation counted in the proof has \(a\) even, \(a+1\) prime, and \(b\) odd. In particular, A400795 has natural density zero.

Paul Erdős and Carl Pomerance studied the same shifted gcd in [“On the Number of False Witnesses for a Composite Number,” *Mathematics of Computation* 46 (1986), 259–279, Theorem 4.1 and (4.2)–(4.4)](https://renyi.hu/~p_erdos/1986-11.pdf). For a general integer \(N\) they estimate \(\sum_{q\mid N,\ q\ {\rm prime}}\log\gcd(q-1,N-1)\) on a set of density one, using counts of prime divisors in progressions. Taking \(N=2(n+1)\) gives the gcd below. Here the statistic counts the factors where this gcd equals one and uses them to construct lattice-point representations.

### 1. A witness from a prime dividing \(n+1\)

Let \(q\) be an odd prime dividing \(n+1\) with \(q<n+1\). Set \(a=q-1\) and \(b=2(n+1)/q-1\). Then \(a\ge2\) is even, \(b\ge3\) is odd, and \((a+1)(b+1)=2(n+1)\). Since \(qb=2(n+1)-q\) and \(q\equiv1\bmod(q-1)\),
\[
\gcd(a,b)=\gcd(q-1,2n+1).
\]
When this gcd is one, \(2P(a,b)=(a+1)(b+1)-2=2n\). Distinct qualifying primes yield distinct unordered representations, because the even coordinate recovers \(q-1\).

### 2. Many primes have few possible obstructions

For an odd prime \(q\) put \(H(q)=\sum_{s\mid q-1,\ s\ {\rm odd\ prime}}1/s\). Fix an integer \(K\ge3\), and let \(W\) be the product of odd primes at most \(K\). Among primes \(q\equiv-1\bmod W\), no odd prime \(s\le K\) divides \(q-1\). We show that those with \(H(q)\le 8/K\) have a divergent sum of reciprocals.

Write \(T(X)=\pi(X;W,-1)\sim X/(\varphi(W)\log X)\), by the prime number theorem in a fixed arithmetic progression. For \(K<s\le X^{1/4}\) prime, the conditions \(q\equiv-1\bmod W\), \(q\equiv1\bmod s\) define one reduced residue class modulo \(Ws\). For \(X\) sufficiently large in terms of \(W\), one has \(Ws\le X^{1/2}\). The [Brun–Titchmarsh inequality](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/BrunTitchmarsh.pdf) bounds the number of such \(q\le X\) by
\[
\frac{2X}{\varphi(W)(s-1)\log(X/(Ws))}
\le\frac{4X}{\varphi(W)(s-1)\log X}.
\]
For each \(q\le X\), the contribution to \(H(q)\) from the prime divisors of \(q-1\) exceeding \(X^{1/4}\) is at most \(4X^{-1/4}\), since the product of four such divisors would exceed \(X\). Consequently
\[
\limsup_{X\to\infty}\frac{1}{T(X)}
\sum_{\substack{q\le X\\q\ {\rm prime},\ q\equiv-1\bmod W}} H(q)
\le4\sum_{\substack{s>K\\s\ {\rm prime}}}\frac1{s(s-1)}
\le4\sum_{m>K}\frac1{m(m-1)}=\frac4K.
\]
By Markov's inequality the lower relative proportion of \(q\) having \(H(q)\le8/K\) is at least \(1/2\) in this progression. In particular, for all sufficiently large \(X\), their counting function is at least \(c_W X/\log X\) for some \(c_W>0\). Partial summation proves divergence of their reciprocal sum. Deleting \(q=2\) or any fixed initial segment does not affect this conclusion.

### 3. Counting unspoiled witnesses

Choose a finite set \(Q\) of these good odd primes with \(L=\sum_{q\in Q}1/q\) as large as desired. For \(n\) uniform modulo the product of the distinct primes occurring in \(Q\) or in any \(q-1\), let \(D\) count the \(q\in Q\) dividing \(n+1\). By the Chinese remainder theorem the divisibility indicators for distinct \(q\) are independent, so \(\mathbb E D=L\) and \(\operatorname{Var}D\le L\).

Let \(B\) count the \(q\in Q\) that divide \(n+1\) but satisfy \(\gcd(q-1,2n+1)>1\). A common prime factor \(s\) must be odd and distinct from \(q\). For each such \(s\mid q-1\), the events \(q\mid n+1\) and \(s\mid2n+1\) have joint probability \(1/(qs)\) by the Chinese remainder theorem. Thus the union bound and linearity of expectation give
\[
\mathbb E B\le\sum_{q\in Q}\frac{H(q)}q\le\frac{8L}{K}.
\]
Chebyshev's inequality gives \(\Pr(D<L/2)\le4/L\), and Markov's inequality gives \(\Pr(B\ge L/4)\le32/K\). Outside these two events \(D-B>L/4\). For \(n>\max Q\), all of these \(D-B\) primes give valid representations by section 1.

The densities of the two exceptional events equal their probabilities since they are periodic. For \(L\ge4h\), the set with fewer than \(h\) representations therefore has upper natural density at most \(4/L+32/K\). For each fixed \(K\) one can take \(L\) arbitrarily large; then letting \(K\) tend to infinity gives upper density zero, as required.

### Scope

The proof addresses the density part of the conjecture. Infinitude for unrestricted inputs remains open in this note. A density-zero set may be finite or infinite. The argument is a mathematical manuscript using the prime number theorem in arithmetic progressions and the Brun–Titchmarsh inequality. Historical priority and a Lean kernel certificate are unconfirmed.

The [prime-factor count](Multiplicity.md) and [products of distinct primes](CompositeWitnesses.md) give more precise estimates for the number of coprime triangle representations. The [exhaustive checker](check_density_witnesses.py) compares the prime construction with direct enumeration of the triangles. Codex prepared this argument for @dwilfand-sys.

The [composite-divisor checker](check_composite_witnesses.py) also compares counts by the number of prime factors. [PrimeWitness.lean](PrimeWitness.lean) is a draft Lean proof of the finite divisor identity. It has no kernel verdict.

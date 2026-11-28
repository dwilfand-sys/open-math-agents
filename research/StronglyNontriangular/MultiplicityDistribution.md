# The limiting distribution of the prime representation count

Let \(R(n)\) count coprime representations \(P(a,b)=n\) in which \(a+1\) is an odd prime, \(a\) is even and \(b\) is odd, with \(a,b>1\). The [prime multiplicity manuscript](Multiplicity.md) derives weak convergence of \(R(n)/\log\log n\), for \(n\) chosen uniformly in \([3,X]\), to the law of
\[
C=\prod_{p\ge3}\left(1-\frac1{p-1}\right)^{U_p},
\qquad \Pr(U_p=1)=1/p,
\]
where the product is over odd primes and the Bernoulli variables are independent. We examine this law. All density statements below use the weak convergence from that manuscript.

**Theorem.** The distribution of \(C\) has no atoms, its topological support is the entire interval \([0,1]\), and it assigns probability one to a Borel set of Hausdorff dimension zero. In particular every open subinterval of \([0,1]\) has strictly positive limiting frequency for \(R(n)/\log\log n\). If \(D(\varepsilon)\) denotes the natural density for which \(R(n)/\log\log n\ge1-\varepsilon\), then
\[
 D(\varepsilon)\sim\frac{2e^{-\gamma}}{\log(1/\varepsilon)}
 \qquad(\varepsilon\downarrow0).
\]
Here the limiting density in \(n\) is taken first.

## Continuity and support

Set \(a_2=0\) and \(a_p=\log((p-1)/(p-2))\) for \(p\ge3\). Then \(a_p\sim1/p\), and \(T=-\log C=\sum_p a_pU_p\) is finite almost surely, since its nonnegative terms have summable expectations. The characteristic function of \(T\) is the Euler product in equation (3) of Paul Erdős's 1939 paper for this choice of \(a_p\). By the continuity condition in equation (4), the divergence of \(\sum_{p\ge3}1/p\) implies that the law has no atoms. Its singularity also follows directly from Erdős's §3, since \(a_p=O(p^{-1})\). Exponentiation is injective and \(t\mapsto e^{-t}\) is Lipschitz on the positive half-line. [Paul Erdős, *On the smoothness of the asymptotic distribution of additive arithmetical functions*, American Journal of Mathematics 61 (1939), 722–725](https://www.renyi.hu/~p_erdos/1939-11.pdf).

For an elementary continuity check, take independent copies \(T,T'\). Among the first \(k\) odd primes let \(H_k\) count the positions where their Bernoulli digits disagree. The discrepancy indicators are independent and have probabilities \(2(1/p)(1-1/p)\) with divergent sum, so \(H_k\to\infty\) almost surely. Conditional on which positions disagree and on all later digits, each of their signs in \(T-T'\) is independently fair. For fixed positive weights, subsets with a specified sum form an antichain. Sperner's theorem bounds the conditional probability of any prescribed value by \(2^{-H_k}\binom{H_k}{\lfloor H_k/2\rfloor}\), tending to zero almost surely. Dominated convergence gives \(\Pr(T=T')=0\), which excludes atoms. Sperner's bound here also follows by counting permutations: a chain of initial subsets of a permutation meets an antichain at most once, and a subset of size \(r\) occurs in exactly \(r!(H_k-r)!\) of these permutations.

For \(s>0\) and \(0<\eta<s\), take \(K\) so large that each \(a_p\) beyond it is less than \(\eta/4\) and \(\mathbb E\sum_{p>K}a_pU_p<\eta/8\). The divergence of \(\sum_{p>K}a_p\) gives a finite consecutive block beyond \(K\) whose sum is in \([s,s+\eta/4)\). Require the digits at primes through \(K\) to be zero and those on the block to be one. This event has positive probability. By independence and Markov's inequality the remaining tail is less than \(\eta/2\) with probability at least \(3/4\). Thus every neighborhood of \(s\) has positive probability. To approximate zero, require all digits through \(K\) to vanish and use the same tail argument. Consequently the support of \(T\) is \([0,\infty)\), and that of \(C\) is \([0,1]\). Weak convergence and the absence of atoms now give limiting frequencies at each fixed interval.

## A full-measure set of Hausdorff dimension zero

We refine the small-product covering argument of Erdős's §3. Fix \(0<\delta<1\) and set \(\alpha=\delta/4\). For \(y\) large define the squarefree product \(Q_y=\prod_{3\le p\le y}p^{U_p}\). The prime Mertens estimates give
\[
 \mathbb E\log Q_{y^\alpha}=\sum_{3\le p\le y^\alpha}\frac{\log p}{p}
 =\alpha\log y+O(1).
\]
Markov's inequality gives \(\Pr(Q_{y^\alpha}\le y^\delta)\ge1/2\) for large \(y\). Independently, all digits in \((y^\alpha,y]\) vanish with probability tending to \(\alpha\), by Mertens's product formula. In particular \(\Pr(Q_y\le y^\delta)\ge c_\delta>0\) uniformly for sufficiently large \(y\).

The tail \(T_{>y}\) has mean \(O(\sum_{n>y}n^{-2})=O(1/y)\). Hence with probability at least \(c_\delta/2\) both \(Q_y\le y^\delta\) and \(T_{>y}\le y^{-1/2}\). On this event \(T\) belongs to the union \(E_y\) of at most \(\lfloor y^\delta\rfloor\) closed intervals of length \(y^{-1/2}\), one starting at \(\sum_{p\mid m}a_p\) for each positive integer \(m\le y^\delta\). The integer \(Q_y\) itself provides the required interval.

Take \(E=\limsup_{j\to\infty}E_{2^j}\). Since the probability of membership in each large-index set is bounded below by \(c_\delta/2\), \(\Pr(T\in E)\ge c_\delta/2\). For every \(s>2\delta\), the sum of the \(s\)-powers of all covering lengths for \(j\ge J\) is bounded by \(\sum_{j\ge J}2^{j(\delta-s/2)}\to0\). Thus \(E\) is Borel and has Hausdorff dimension at most \(2\delta\).

Let \(G\) be the countable additive group generated by the \(a_p\), and put \(F=E+G\). This Borel set has the same dimension bound. For every finite initial set of digits, deleting their contribution to \(T\) changes \(T\) by an element of \(G\), leaving membership in \(F\) unchanged. Therefore \(\{T\in F\}\) is a tail event up to the null set of nonconvergence. Kolmogorov's zero-one law and the positive lower bound give \(\Pr(T\in F)=1\). Intersect such full-measure sets over a sequence \(\delta\downarrow0\) to obtain a Borel set of dimension zero carrying \(T\). Its intersection with \([0,\infty)\) maps homeomorphically into \((0,1]\) under the Lipschitz map \(t\mapsto e^{-t}\), giving the assertion for \(C\).

## The frequency near the upper endpoint

Write \(t=-\log(1-\varepsilon)\). For small \(t\), the event \(T\le t\) implies all digits at odd primes \(p\le1/t\) vanish, because \(a_p>\frac1{p-1}>t\) there. Mertens's product formula gives the upper bound
\[
 \Pr(T\le t)\le\prod_{3\le p\le1/t}(1-1/p)
 \sim\frac{2e^{-\gamma}}{\log(1/t)}.
\]
The factor 2 comes from omitting the prime 2. For the lower bound require all odd digits through \(2/t\) to vanish. This event has the same asymptotic probability and is independent of the later digits. Using \(a_p\ll1/p\) and partial summation from the elementary estimate \(\pi(x)\ll x/\log x\) gives
\[
 \mathbb E T_{>2/t}\ll\sum_{p>2/t}\frac1{p^2}
 \ll\frac{t}{\log(1/t)}.
\]
Markov's inequality now gives \(\Pr(T_{>2/t}\le t)=1-o(1)\). Both bounds agree, and \(t\sim\varepsilon\). Finally, absence of atoms gives \(D(\varepsilon)=\Pr(T\le t)\).

Codex derived these consequences for @dwilfand-sys from the research manuscript on the triangle problem of Petersen, Validashti and Wayland. Erdős and his predecessors established the general continuity and singularity results above. Historical priority for the dimension and endpoint refinements has not been determined. The derivations have no Lean compilation verdict.

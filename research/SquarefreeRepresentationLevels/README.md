# Finiteness of the A085263 representation levels

Let \(R(n)\) be the number of positive integers \(a\) with \(a^2<n\) and \(n-a^2\) squarefree. Each such \(a\) determines one representation. Robert G. Wilson v's conjecture asks that every level have finitely many positive inputs and identifies 1 and 13 as the inputs with count zero. The formal statement uses these two assertions. [OEIS A085263 source](https://github.com/oeis/oeisdata/blob/main/seq/A085/A085263.seq)

## Proof

For the finiteness claim the classical representation asymptotic suffices. For each fixed \(\epsilon>0\), Section 4 of Jiménez Urroz gives
\[
 R(n)=\sqrt n\,\prod_p(1-g_p(n)/p^2)+O_\epsilon(n^{1/3+\epsilon}),
\qquad
 g_p(n)=\#\{a\bmod p^2:a^2\equiv n\bmod p^2\}.
\]
Dropping a possible zero square changes the count by at most one. The product is \(\gg 1/\log\log n\), uniformly as \(n\) tends to infinity. For completeness, at an odd prime dividing \(n\) to exponent at least two the factor is \(1-1/p\). At every other odd prime it is at least \(1-2/p^2\), and at 2 it is at least \(1/2\). Put \(y=\log n\). For the exceptional \(p>y\), there are at most \((\log n)/(2\log y)\) of them and \(\sum 1/p\le (\log n)/(2y\log y)=o(1)\). The product at the remaining \(p>y\) is also \(1-o(1)\), by convergence of \(\sum_{m>y}2/m^2\). For \(p\le y\), the factors are all at least \(1-1/p\). Mertens' product theorem gives the claimed bound. Taking, for example, \(\epsilon=1/12\) now yields \(R(n)\to\infty\). Given a level \(k\), choose \(N_k\) so \(n\ge N_k\) implies \(R(n)>k\); the level is a subset of \(\{1,\ldots,N_k-1\}\). [Jiménez Urroz, Section 4](https://arxiv.org/pdf/2010.15580) · [Published article](https://doi.org/10.1016/j.exmath.2021.12.002)

The zero-level conclusion needs a separate uniform argument. At \(n=1\) there is no candidate. At \(n=13\) the three positive differences are \(12,9,4\), each divisible by a prime square. Conversely, the constructive sieve for A085265 supplies a positive root \(a\) with squarefree positive difference for every other \(n>0\). In particular \(a^2<n\) implies \(a\le\lfloor\sqrt n\rfloor\), so the filtered finite set used to define \(R\) contains \(a\). This proves the equality of sets. [Constructive sieve for the exact zero exceptions](https://github.com/dwilfand-sys/open-math-agents/blob/acedc78ebba2903e02b4361c4c7e95e6dafdb367/proofs/oeis-a085265.lean)

## Elementary route for Lean

The analytic asymptotic need not be imported into a Lean proof. The existing elementary sieve gives an alternative quantitative result in terms of \(u=\lfloor\sqrt{n-1}\rfloor\), the number \(J\) of positive roots of the selected parity in \([1,u]\), and the number \(r\) of odd prime squares dividing \(n\). We have \(u\le2J+1\) and \(3^r\le2J+2\). For \(J\ge10^6,\ r\le9\), the table of three rational estimates in §3 of the linked proof gives increasing affine lower bounds for \(R(n)\) with strictly positive slopes. For \(r\ge10\), its bound is \(r R(n)\ge27J/400\). Thus for any given \(k\), split at a sufficiently large fixed \(r_0\). At \(10\le r<r_0\) the last bound grows linearly in \(J\); at \(r\ge r_0\), the existing auxiliary estimate \(J\ge4r8^r\) gives \(R(n)\ge(27/100)8^r>k\). This avoids using any real logarithm in the formal proof. Since \(J\to\infty\) with \(n\), combine the resulting threshold with the elementary finite-set argument above. Use the injection \(x\mapsto 2x+b\) from surviving parity candidates into the filtered set of roots before applying the card bound. [Complete quantitative estimates and independently reproduced finite checks](https://github.com/dwilfand-sys/open-math-agents/blob/99ef40433a191e22afa308e3ea1980bc92aeebf7/research/SquarefreeRepresentationCounts/README.md)

One can even give an explicit polynomial bound using this same argument. Put
\[
 B(k)=100(k+300000)+15k^2.
\]
If \(R(n)\le k\), then \(n\le(2B(k)+2)^2\). Indeed, when \(J\ge10^6,\ r\le9\), every one of the three lower bounds in §3 implies \(R(n)\ge J/100-300000\). The respective slopes after the cutoff loss are \(36/125-1/4-1/128,\ 34/125-1/4-1/128,\ 1/4-2/9-1/128\), each larger than \(1/100\). Each constant loss is at most \(262145+1+61\cdot512<300000\). At \(r\ge10\), \(100R(n)\ge27\cdot8^r\) with \(8^r\ge4r\), so \(r\le R(n)\). Then \(27J\le400rR(n)\le400k^2\), giving \(J\le15k^2\). The case \(J<10^6\) is already covered by \(J\le B(k)\). Finally \(n\le(u+1)^2\le(2J+2)^2\), proving the claimed bound. Thus the formal finiteness target can be obtained directly by a subset of a single explicit finite interval.

The [exact checks](check_levels.py) verify all rational comparisons in the uniform bound and independently enumerate the first 10,000 representation counts. In this segment all 25 stated first occurrences and all 11 displayed frequency counts agree. The companion 101-level proof establishes where the complete finite frequencies terminate. The Lean candidate imports our [submitted statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13205). The candidate passed the repository's static gate; the pinned kernel has not verified it. Codex developed the explicit bound and finite-set formalization for @dwilfand-sys. The historical asymptotic is credited above, and the source statement on the A085265 zero exceptions was previously formalized by @niclorusso.

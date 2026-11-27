# The cubic congruence for Hanna's A181069

For \(N\ge1\), Paul D. Hanna's sequence has the finite formula
\[
a(N)=\sum_{j=0}^{N-1}\binom{N-1}{j}^{3}\binom Nj.
\]
The formula appears in OEIS A181069, where Peter Bala conjectured the following congruence on August 4, 2026.

**Theorem.** If \(p\ge5\) is prime and \(p\mid N\), then
\[
a(N)\equiv a(N/p)\pmod {p^{3v_p(N)}}.
\]
In particular, for positive \(n,r\), \(a(np^r)\equiv a(np^{r-1})\pmod{p^{3r}}\). The version with \(v_p(N)\) includes the case \(p\mid n\) without any coprimality convention. [OEIS A181069](https://oeis.org/A181069)

Write \(r=v_p(N)\ge1\) and \(M=N/p\). Congruences of rational numbers below take place in the ring \(\mathbb Z_{(p)}\) of rationals whose reduced denominators are prime to \(p\).

## Symmetry

Let \(B(N,j)=\binom Nj\). At interior indices \(1\le j<N\), put
\[
U(N,j)=\binom{N-1}{j-1}=\frac{j}{N}B(N,j),\qquad
V(N,j)=\binom{N-1}{j}=\frac{N-j}{N}B(N,j).
\]
Reflection \(j\mapsto N-j\) and \(x^3+(1-x)^3=1-3x(1-x)\) give
\[
2a(N)=2+\sum_{1\le j<N} T(N,j),\qquad
T(N,j)=B(N,j)^4-3B(N,j)^2U(N,j)V(N,j).
\tag{1}
\]
Indeed the original term is \(V^3 B\), its reflection is \(U^3B\), and \(U+V=B\). The two endpoint terms of the reflected sum are 1 each. All summands \(T\) are integers.

## Reciprocal squares

Define \(H(t)=\sum_{1\le i\le t,\ p\nmid i}i^{-2}\), with \(H(0)=0\). If \(p^s\mid t\), then
\[
H(t)\equiv0\pmod{p^s}.
\tag{2}
\]
For \(s=0\), this is integrality in \(\mathbb Z_{(p)}\). If \(s>0\), each complete interval of length \(p^s\) contains each unit residue modulo \(p^s\) exactly once. Multiplication by 2 permutes the units. Thus the sum of their inverse squares equals one quarter of itself modulo \(p^s\). The factors 3 and 4 are invertible because \(p\ge5\).

## Indices divisible by \(p\)

For \(0<j<N\) with \(p\mid j\), put \(s=\min(v_p(j),r)\), \(v=j/p\), and
\[
R=\frac{B(N,j)}{B(M,v)}.
\]
We need
\[
R\equiv1\pmod{p^{r+2s}}.
\tag{3}
\]
This is a special case of the classical Jacobsthal–Kazandzidis congruence. We give the finite-product proof to show exactly the precision used. In the factorial product for \(\binom{N}{j}\), separate the factors whose indices are divisible by \(p\). Since \(j\) is divisible by \(p\), there are \(j-j/p\) remaining indices, an even number. Therefore
\[
R=\prod_{\substack{1\le i<j\\p\nmid i}}(1-N/i).
\]
Pair \(i\) with \(j-i\). This involution has no fixed point as \(p\) is odd and \(p\mid j\). Each paired factor is \(1+D/(i(j-i))\) with \(D=N(N-j)\). Because \(p^s\) divides \(j\) and \(N\), \(v_p(D)\ge r+s\). Terms with two or more factors \(D\) vanish modulo \(p^{r+2s}\). Twice the reciprocal sum over the pairs satisfies
\[
2\sum_{\rm pairs}\frac1{i(j-i)}
 =\sum_{\substack{1\le i<j\\p\nmid i}}\frac1{i(j-i)}
 \equiv-\sum_{\substack{1\le i<j\\p\nmid i}}i^{-2}
 =-H(j)\equiv0\pmod{p^s}.
\]
Here \(j-i\equiv-i\bmod p^s\). The factor 2 is invertible. Thus the linear term also vanishes, proving (3).

At the two levels \(N,j\) and \(M,v\), all three binomial factors \(B,U,V\) are multiplied by the same ratio \(R\), since \(j/N=v/M\). Thus \(T(N,j)=R^4T(M,v)\). The integer \(B(M,v)\) has valuation at least \(r-s\): for \(v_p(j)<r\) use \(vB(M,v)=M\binom{M-1}{v-1}\), and otherwise the bound is zero. The factor \(B(M,v)^2\) in both terms of \(T(M,v)\) gives \(v_p(T(M,v))\ge2(r-s)\). Finally \(R^4-1\) is divisible by \(p^{r+2s}\) by (3). Consequently
\[
T(N,j)-T(M,v)\equiv0\pmod{p^{3r}}.
\tag{4}
\]

## Indices coprime to \(p\)

For such \(j\), put \(W_j=U(N,j)^4\). We have \(B(N,j)=(N/j)U(N,j)\) and \(V(N,j)=((N-j)/j)U(N,j)\). Hence
\[
T(N,j)=W_j\left(\frac{N^4}{j^4}-\frac{3N^3}{j^3}+\frac{3N^2}{j^2}\right)
\equiv3N^2 W_j/j^2\pmod{p^{3r}}.
\tag{5}
\]
We show that the sum of the remaining reciprocal terms is divisible by \(p^r\). Define \(W_j=\binom{N-1}{j-1}^4\) at every \(1\le j\le N\). The adjacent weights have the following precision, where again \(s=\min(v_p(j),r)\):
\[
W_{j+1}-W_j\equiv0\pmod{p^{r-s}}\qquad(1\le j<N).
\tag{6}
\]
If \(s=r\), this follows from integrality. If \(s<r\), the ratio identity gives \(W_{j+1}=W_j(1-N/j)^4\), and \(N/j\in p^{r-s}\mathbb Z_{(p)}\).

Discrete summation by parts yields
\[
\sum_{\substack{1\le j\le N\\p\nmid j}} W_j/j^2
=W_NH(N)-\sum_{j=1}^{N-1}(W_{j+1}-W_j)H(j).
\tag{7}
\]
The endpoint term is divisible by \(p^r\) by (2). For each interior term (2) supplies \(p^s\), while (6) supplies \(p^{r-s}\). This proves that the entire left side of (7) is divisible by \(p^r\). Since \(p\mid N\), including \(j=N\) does not add an unaligned term. Equation (5) now gives
\[
\sum_{\substack{1\le j<N\\p\nmid j}} T(N,j)\equiv0\pmod{p^{3r}}.
\tag{8}
\]
By (1), (4) and (8), \(2a(N)\equiv2a(M)\pmod{p^{3r}}\). Inverting 2 proves the theorem.

## Sources and prior results

- Osburn, Sahu and Straub, *Supercongruences for sporadic sequences*, Lemmas 2.1–2.3, give Jacobsthal scaling, the reciprocal-unit sum and the gain from powers of a lower-level binomial factor. Their proof of Theorem 1.2 also uses cancellation over blocks of unit reciprocals for a different family. Here the symmetry in (1) and the adjacent-weight summation in (5)–(7) treat Hanna's shifted fourth-power sum. [Author manuscript](https://researchrepository.ucd.ie/server/api/core/bitstreams/7a77d4a0-e176-4bc7-8cb8-acd091420042/content).
- Tamás Lengyel, *p-adic convergence of sums of powers of binomial coefficients*, Theorem 3.5, states the classical Jacobsthal–Kazandzidis relative congruence. [Paper](https://www.mathstat.dal.ca/FQ/Papers1/55-5/Lengyel.pdf).
- The upstream proof by @TheWaler for a different sequence already implements the exact Robert–Zuber ratio behind (3). Daniel Whorlow (@draonbioetl) and @coracle-us have also implemented, respectively, the complementary-pair method and the binomial ratio with exact valuations for A003161. [Accepted Robert–Zuber implementation](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/main/proofs/OeisA208425.conjecture_1.lean) · [Whorlow's finite-pair proof](https://github.com/draonbioetl/open-math-agents/blob/e13808fbf064e066409c851be30eff6846c8fb97/proofs/oeis-a003161.lean#L722) · [Ratio implementation](https://github.com/coracle-us/open-math-agents/blob/961574a26c69794ca342ad2d800c32661f250d1f/proofs/oeis-a003161.lean#L1795).
- A search of @rbajaj5's 110-record campaign ledger and public repository at commit e6955c6a329a713e7ed7b3f1dca165f587131c90 yielded no occurrence of A181069. This is a bounded priority search. [Campaign ledger](https://github.com/rbajaj5/a183068-supercongruence/blob/e6955c6a329a713e7ed7b3f1dca165f587131c90/data/bala_110_campaign.tsv).

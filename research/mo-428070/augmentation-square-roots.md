# Square roots in the augmentation ideal of a finite rational group algebra

Hugo MTV asked whether the rational group algebra of a finite group \(G\) contains a square root of \(2\), and whether its augmentation ideal contains a square root of twice its own unit. For the first question JP McCarthy observed that the trivial representation sends such a root to a rational square root of \(2\). The author then specifically asked about the augmentation ideal. [Original question and exchange, August 2022](https://mathoverflow.net/questions/428070/existence-of-sqrt2-in-a-finite-group-algebra-over-mathbbq)

**Answer to the second question.** The trivial group gives the degenerate solution \(u=x=0\). For every nontrivial finite group, the equation \(x^2=2u\) is impossible. Here
\[
e_G=|G|^{-1}\sum_{g\in G}g,\qquad u=1-e_G.
\]
The rational algebra \(I_G=\ker\varepsilon\) has identity \(u\), where \(\varepsilon(\sum a_g g)=\sum a_g\). The argument below also classifies all rational nonsquares in place of \(2\).

## Short proof for 2 using the trace

Suppose \(x^2=2u\). Right multiplication by \(x\) makes \(I_G\) a vector space over \(K=\mathbb Q(\sqrt2)\). Every left multiplication \(L_g\) is \(K\)-linear and has finite order. Its \(K\)-linear trace is a sum of roots of unity, so it is an algebraic integer in \(K\). Every such integer belongs to \(\mathbb Z[\sqrt2]\) and has even trace down to \(\mathbb Q\). By restriction of scalars, the rational trace of \(L_g\) on \(I_G\) is therefore an even integer.

Choose any \(g\ne1\). On \(\mathbb Q[G]\) the same translation permutes the basis with no fixed points, so its trace is zero. On the trivial summand \(\mathbb Qe_G\) its trace is one. Its trace on the complementary augmentation ideal is therefore \(-1\), a contradiction.

The even-trace fact can also be seen directly. For an algebraic integer \(a+b\sqrt2\) with \(a,b\in\mathbb Q\), its trace \(m=2a\) and norm \(n=a^2-2b^2\) are integers. If \(m\) were odd, \(m^2-4n=8b^2\) would be an odd integer. For \(b\ne0\) its right-hand side has odd 2-adic valuation, whereas the left side has valuation zero. For \(b=0\) the right-hand side vanishes.

## A determinant proof that also works for other nonsquares

Suppose \(G\ne1\) and \(x^2=2u\). Applying \(\varepsilon\) gives \(\varepsilon(x)=0\). On \(I_G\), right multiplication by \(x\) squares to twice the identity. Consequently \(I_G\) is a vector space over \(\mathbb Q(\sqrt2)\). Its rational dimension is \(|G|-1\), so \(|G|\) is odd.

Choose an element \(g\) of odd prime order \(p\) by Cauchy's theorem. Extend scalars to \(K=\mathbb Q(\zeta_p)\) for a primitive \(p\)-th root \(\zeta_p\), and consider left multiplication by \(g\) on \(K[G]\). Each set \(\langle g\rangle t\) of basis elements is one \(p\)-cycle. It supplies exactly one dimension of the \(\zeta_p\)-eigenspace \(V\), spanned on that cycle by
\[
\sum_{j=0}^{p-1}\zeta_p^{-j}g^j t.
\]
Thus \(\dim_K V=d=|G|/p\) is odd. Every vector in \(V\) has augmentation zero, since \(\varepsilon(gy)=\varepsilon(y)=\zeta_p\varepsilon(y)\). Right multiplication by \(x\) commutes with left multiplication by \(g\), so it preserves \(V\). Its restriction \(T\) satisfies \(T^2=2\,\mathrm{id}_V\). Taking determinants gives
\[
\left(\frac{\det T}{2^{(d-1)/2}}\right)^2=2.
\]
But \(K\cap\mathbb Q(\zeta_8)=\mathbb Q\). Indeed the compositum is \(\mathbb Q(\zeta_{8p})\) of degree \(\varphi(8p)=\varphi(8)\varphi(p)\). Since \(\sqrt2=\zeta_8+\zeta_8^{-1}\) for \(\zeta_8=e^{\pi i/4}\), a root of \(2\) in \(K\) would contradict that intersection.

## The same question for any rational nonsquare

Let \(c\in\mathbb Q^\times\) be a nonsquare and \(G\) be a nontrivial finite group. Then
\[
\exists x\in I_G,\ x^2=c\,u
\quad\Longleftrightarrow\quad
G\text{ is a }p\text{-group for an odd prime }p
\text{ and }c=(-1)^{(p-1)/2}p\,s^2\text{ for some }s\in\mathbb Q^\times.
\]

For necessity, replace \(2\) by \(c\) in the dimension and determinant argument. The order of \(G\) is odd and \(\mathbb Q(\sqrt c)\) embeds in \(\mathbb Q(\zeta_p)\) for every prime \(p\mid |G|\). The unique quadratic subfield of \(\mathbb Q(\zeta_p)\) is \(\mathbb Q(\sqrt{p^*})\), where \(p^*=(-1)^{(p-1)/2}p\). Two distinct odd primes give different square classes by unique factorization. This forces the stated condition.

For sufficiency it is enough to construct a root for \(c=p^*\), then multiply by \(s\). Induct on the order of a finite \(p\)-group, using the zero root when the group is trivial. In a nontrivial group choose a central subgroup \(H=\langle h\rangle\) of order \(p\). Write \(e_H=p^{-1}\sum_{h'\in H}h'\), let \(\chi\) be the Legendre symbol extended by \(\chi(0)=0\), and put
\[
t_H=\sum_{a=0}^{p-1}\chi(a)h^a.
\]
The coefficient sum of \(t_H\) is zero, so \(t_H e_H=e_H t_H=0\). The Gauss sum identity gives \(t_H^2=p^*(1-e_H)\). To see the identity in the group algebra, evaluate at every character \(h\mapsto\zeta_p^k\). The value of \(t_H\) at \(k=0\) is zero. For \(k\ne0\) it is \(\chi(k)\tau\), where \(\tau=\sum_a\chi(a)\zeta_p^a\) satisfies \(\tau^2=p^*\). Character evaluation is injective on \(\mathbb Q[H]\).

The map \(\mathbb Q[G/H]\longrightarrow e_H\mathbb Q[G]\) sending \(\bar g\) to \(e_H g\) is an algebra isomorphism with identity \(e_H\). It carries the average of \(G/H\) to \(e_G\). Applying it to the inductive root gives an element \(y\) with \(y^2=p^*(e_H-e_G)\). Since \(y=e_Hy=ye_H\), both cross terms with \(t_H\) vanish. Consequently \((t_H+y)^2=p^*(1-e_G)\), as required.

The pinned Lean kernel verified both parts for the scalar 2, including the trivial-group exception, with only `propext`, `Classical.choice` and `Quot.sound`. JP McCarthy gave the full-algebra observation. Claude Code formalized that observation, and Codex proved and formalized the augmentation-ideal result for @dwilfand-sys. The general square-class and number-field classifications remain paper results. Historical priority for the augmentation-ideal answer is undetermined. [Exact statement](https://github.com/dwilfand-sys/open-math-agents/blob/36a191e2e3c6ece898ce6c468d4bbfa51cc7294f/statements/mo-428070.lean) · [Exact proof](https://github.com/dwilfand-sys/open-math-agents/blob/c521c2f1fa6880b9c08082b12788945eb16cd99b/proofs/mo-428070.lean) · [Pristine verifier verdict](https://github.com/dwilfand-sys/open-math-agents/actions/runs/46090875717/job/140811223697)

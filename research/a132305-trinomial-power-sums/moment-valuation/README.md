# Power-sum supercongruences for the A132305 trinomial rows

Write \(c(N,j)=[x^j](1+x+x^2)^N\) and \(A_h(N)=\sum_{j=0}^{2N}c(N,j)^h\). For every prime \(p\ge5\), positive \(N\) divisible by \(p\), and integer \(h\ge2\), put \(\alpha=v_p(N)\) and \(b=v_p(h)\). Then

\[
A_h(N)\equiv A_h(N/p)\pmod{p^{2\alpha+b}}.
\]

The Lean theorem `A132305.moment_full_valuation` writes \(N=np^k\), with \(n,k>0\), and its exponent is \(2(k+v_p(n))+v_p(h)\). Taking \(k=1\), \(n=N/p\) gives the form above. Taking \(h=5\) gives the original statement and an extra factor of five at \(p=5\). The Lean row sum uses `Finset.range (2*N+1)`. It includes \(j=0\) and \(j=2N\); for \(N=1\) it equals three.

## Why the exponent increases

The accepted proof gives two coefficient estimates. At the indices \(p j\), the coefficients \(c(N,pj)\) and \(c(N/p,j)\) agree modulo \(p^{2\alpha}\). At every remaining index \(i\), \(p^\alpha\) divides \(c(N,i)\). The new Lean proof reuses the accepted finite-product derivation of both estimates.

If \(x\equiv y\bmod p^s\) and \(s>0\), factor \(y^p-x^p\) into \(y-x\) times its geometric sum. Modulo \(p\), all \(p\) terms of the sum agree. This gains one digit each time we raise to the \(p\)-th power. Iterating \(b\) times and raising to \(h/p^b\) proves the claimed modulus at every index \(pj\). At each other index, the \(h\)-th power is divisible by \(p^{\alpha h}\). The inequality \(\alpha h\ge2\alpha+b\) follows from \(h\ge2+b\), since \(p^b\mid h\), \(p\ge5\), and \(h\ge2\). The indices \(0,p,\ldots,2N\) map bijectively to \(0,1,\ldots,2N/p\).

## The bound is attained for every exponent at row five

For every \(h\ge2\) one has \(v_5(A_h(5)-A_h(1))=2+v_5(h)\). This sharpness statement has the following elementary proof. The complete fifth row is

\[
(1,5,15,30,45,51,45,30,15,5,1).
\]

For \(h=2\), the difference is \(8950=25\cdot358\). For \(h\ge3\), write \(h=5^bu\), \(5\nmid u\). Every coefficient away from positions \(0,5,10\) is divisible by five, so its \(h\)-th power vanishes modulo \(5^{b+3}\). Indeed, \(h\ge3\) when \(b=0\), and \(5^b\ge b+3\) for \(b\ge1\). This leaves \(51^h-1\). In the binomial expansion \(51^u=(1+50)^u\), terms of degree at least two vanish modulo \(125\). Thus \(51^u=1+25c\) with \(c\equiv2u\bmod5\). If \(t\ge2\), binomial expansion gives \((1+5^tc)^5\equiv1+5^{t+1}c\bmod 5^{t+2}\). After \(b\) such steps the quotient \((A_h(5)-3)/5^{b+2}\) has residue \(2u\bmod5\), which is nonzero. This precludes a uniformly stronger modulus even with the prime and row fixed. The separate sharpness argument is on paper.

## Reproduction and credit

The pinned Lean kernel accepted the complete candidate on 28 November 2026 at fork commit `255d5e7ab61cbedabd0dab4d84eae834188ec264`, proof blob `48a25687a1c8f629bc82c54e7756a3377450375a`. The artifact `15238794786` records the audited dependencies `propext`, `Classical.choice`, and `Quot.sound`. The original theorem directly invokes `A132305.moment_full_valuation` before weakening the modulus. The fifth-row sharpness proof above was independently checked on paper. This directory contains the [exact accepted Lean source](oeis-a132305.lean) and the [original verifier output](verdict.json). The original verdict JSON has SHA-256 `3f61fb5d33c0fc082ca84d55b2a3e2e61c208fdd9c4c4efd031d7aded554e97c`. [Pinned check](https://github.com/dwilfand-sys/open-math-agents/actions/runs/46086751118) · [Exact Lean source](https://github.com/dwilfand-sys/open-math-agents/blob/255d5e7ab61cbedabd0dab4d84eae834188ec264/proofs/oeis-a132305.lean#L714)

Apply [the patch](A132305MomentValuation.patch) to `proofs/oeis-a132305.lean` at Git blob `7cb1b67d790bcd8b992bf6eb388894cbf472641a`. The complete candidate uses the original statement unchanged and derives its conclusion from the full valuation theorem. The fork precheck has exactly one changed proof file. [Accepted proof used as the base](https://github.com/dwilfand-sys/open-math-agents/blob/a5cdbda9a24cce1810b8ed7c15361820ee795c42/proofs/oeis-a132305.lean) · [Upstream PR 13072](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13072) · [Fork verification PR 25](https://github.com/dwilfand-sys/open-math-agents/pull/25)

From this directory run `python check_a132305_moment_valuation.py`. The accompanying `check_a132305_tower.py` provides the independent multinomial formula. It compares every coefficient in 14 adjacent row pairs against a separate multinomial evaluation, checks 121 distinct lifted congruences, and checks the sharp valuation and leading digit for 106 fifth-row exponents. These include all \(2\le h\le100\) and exponents as large as \(5^9\).

The [existing coefficientwise research note](https://github.com/dwilfand-sys/open-math-agents/blob/a6637da326c38c0f49d50587b6d94dbfc04f89c6/research/a132305-trinomial-power-sums/README.md) already states the lifted formula and its formal-series proof. The [companion first-digit formula](https://github.com/dwilfand-sys/open-math-agents/blob/a6637da326c38c0f49d50587b6d94dbfc04f89c6/research/a132305-trinomial-power-sums/first-digit.md) also establishes the sharpness example on paper in greater generality. The calculation above independently verifies its fifth-row case. The contribution here is the Lean formalization for every exponent via the accepted finite-product coefficient bounds. Codex produced it for @dwilfand-sys. Peter Bala posed the OEIS fifth-power congruence, and @sntntHb formalized the competition statement. The research note credits @rbajaj5 for an earlier public proof of the cube case and the cyclotomic reduced-logarithm identity underlying the formal-series approach. Historical priority for the broader congruence has not been established. [OEIS A132305](https://oeis.org/A132305) · [Earlier cube proof](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md)

# A coefficientwise proof for sums of powers of trinomial coefficients

The two exceptional primes have separate proofs. At prime two, [the dyadic valuation](dyadic-valuation.md) is exact for every row divisible by four and every exponent at least three. At prime three, [the ternary extension](ternary-extension.md) recovers the full modulus for every row divisible by 27 and every exponent at least three.

Let \(F(x)=1+x+x^2\), \(t(N,j)=[x^j]F(x)^N\), and \(A_h(N)=\sum_{j=0}^{2N}t(N,j)^h\). Peter Bala conjectured the following congruence for cubes, fourth powers, and fifth powers on 29 August 2025. [A132303](https://oeis.org/A132303), [A132304](https://oeis.org/A132304), [A132305](https://oeis.org/A132305).

An earlier public proof by [@rbajaj5](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md) solves the cube case by using a reduced Frobenius logarithm and a two-variable constant term. That work already gives the crucial logarithm and the factorial valuation estimate below. We independently obtained the same mechanism while considering fifth powers. The following univariate formulation records its effect on each individual trinomial coefficient and resolves all the power sums at once. We make no claim to historical priority for these consequences. Hao Pan and Zhi-Wei Sun had earlier obtained the central-coefficient congruence, with more precise information modulo higher powers. [Pan and Sun](https://arxiv.org/abs/2012.05121).

The same author's [cyclotomic rational-framing theorem](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/CyclotomicRationalFramingTower.md) already establishes the univariate reduced-logarithm identity and its support for general finite cyclotomic products. Reading its proof at every multiple-of-\(p\) index supplies the coefficient estimate used here. Their [public 110-record ledger](https://github.com/rbajaj5/a183068-supercongruence/blob/main/data/bala_110_campaign.tsv) explicitly lists A132303. Our contribution here is the simultaneous power-sum deduction, its explicit application to Bala's fourth- and fifth-power entries, and the further elementary lifting observation below.

**Coefficient theorem.** Let \(p\ge5\) be prime, \(k,n\ge1\), \(N=np^k\) and \(M=N/p\). For every \(j\ge0\),
\[
t(N,pj)\equiv t(M,j)\pmod{p^{2k}},\qquad
p\nmid j\ \Longrightarrow\ p^k\mid t(N,j).
\]
Consequently \(A_h(N)\equiv A_h(M)\pmod{p^{2k}}\) for every integer \(h\ge2\). This includes the complete fifth-power conjecture in the project's A132305 statement.

**Proof.** All logarithms and exponentials below are formal power series over \(\mathbb Q\), applied to series of constant term one and zero, respectively. Integers localized at \(p\), written \(\mathbb Z_{(p)}\), are the rationals whose reduced denominators are prime to \(p\). Every operation on series is coefficientwise finite where required.

Because \(F(x)=(1-x^3)/(1-x)\),
\[
\log F(x)=\sum_{m\ge1}c_m\,\frac{x^m}{m},
\qquad c_m=1-3{\bf1}_{3\mid m}.
\]
Since \(p\ne3\), \(c_{pm}=c_m\). The terms with \(p\mid m\) therefore cancel exactly in \(p\log F(x)-\log F(x^p)\), leaving \(pS(x)\), where
\[
S(x)=\sum_{\substack{m\ge1\\p\nmid m}}c_m\,x^m/m\in x\mathbb Z_{(p)}[[x]].
\]
It follows that \(F(x)^N=F(x^p)^M\exp(NS(x))\).

For \(r\ge2\), one has \(v_p(r!)\le r-2\). For \(r=2\) this follows from \(p>2\); for \(r\ge3\) use \(v_p(r!)\le(r-1)/(p-1)\le r-2\). Thus
\[
 v_p(N^r/r!)\ \ge\ kr-r+2=2k+(r-2)(k-1)\ge2k.
\]
As \(S\) has zero constant term, only finitely many \(r\) enter any given coefficient of the exponential, so
\[
F(x)^N\equiv F(x^p)^M(1+NS(x))\pmod{p^{2k}\mathbb Z_{(p)}[[x]]}.
\]
Every degree in \(F(x^p)^M\) is divisible by \(p\), and every degree in \(S\) is prime to \(p\). Their product has no terms of degree divisible by \(p\). Reading those degrees gives the first congruence. At the other degrees the first term vanishes and the linear term is a multiple of \(p^k\), proving the second. Congruences between the resulting integer coefficients in \(\mathbb Z_{(p)}\) are ordinary integer congruences.

In \(A_h(N)\), the terms at indices not divisible by \(p\) vanish modulo \(p^{2k}\), since \(h\ge2\). Raising the coefficient congruence to the \(h\)-th power handles every remaining term. The indices \(0,p,\ldots,2N\) correspond bijectively to \(0,1,\ldots,2M\), proving the assertion.

**Extra precision for the fifth powers at five.** In fact put \(\alpha=v_p(N)\) and \(b=v_p(h)\). Then
\[
A_h(N)\equiv A_h(N/p)\pmod{p^{2\alpha+b}}.
\]
Apply the coefficient theorem with \(k=\alpha\). If \(u\equiv v\bmod p^t\) for \(t\ge1\), then \(u^p\equiv v^p\bmod p^{t+1}\), by the binomial expansion of \((v+(u-v))^p\); no unit hypothesis is required. Write \(h=p^bh_0\), raise first to \(h_0\), then iterate the \(p\)-power implication \(b\) times. This proves the sharper congruence at every multiple-of-\(p\) index. Every other term is divisible by \(p^{\alpha h}\), and \(\alpha(h-2)\ge b\) for \(h\ge2\) and \(p\ge5\). In particular A132305 satisfies the modulus \(5^{2\alpha+1}\) at \(p=5\). For \(N=5,\ h=5\) the valuation is exactly 3, so the extra digit is attained sharply. The same argument works at any fixed higher power divisible by \(p\).

**Generalization.** With the same proof the polynomial can be replaced by \(1+x+\dots+x^{d-1}\) when \(p\) is odd and \(p\nmid d\): simply replace \(3\) by \(d\) throughout. More generally the argument applies to an integral polynomial with constant term one whose logarithmic coefficients \(c_m=m[x^m]\log F(x)\) are \(p\)-integral and satisfy \(c_{pm}=c_m\). Many products or quotients of factors \(1-x^d\), \(p\nmid d\), have this property. The polynomial condition makes row sums finite. No Lean kernel verdict is claimed.

**Finite verification.** The accompanying standard-library Python checker multiplies polynomials modulo the relevant prime powers using an integer radix chosen to preclude coefficient carries. It checks 69 adjacent row pairs, 130,501 coefficients, and 414 power-sum congruences for primes from 5 through 19, including levels up to five. A second evaluation by counting words with fixed numbers of zeros, ones, and twos independently reproduced 4,560 coefficients. In the sharp example \(A_5(5)=764206503\) and \(A_5(1)=3\). These calculations complement the proof.

# Trinomial row moments and earlier congruences

Write \(F(x)=1+x+x^2\), \(t(N,j)=[x^j]F(x)^N\), and
\(A_h(N)=\sum_{j=0}^{2N}t(N,j)^h\). For every prime \(p\ge5\), positive
multiple \(N\) of \(p\), and integer \(h\ge2\), the theorem checked in Lean
on the research fork gives
\[
  A_h(N)\equiv A_h(N/p)\pmod{p^{2v_p(N)+v_p(h)}}.
\]
The following deduction from the classical binomial scaling congruence
clarifies the mathematical provenance of the estimate. It also gives an
alternative to the elementary binomial-pair proof used in the Lean file.
[Lean proof and check](https://github.com/dwilfand-sys/open-math-agents/pull/25)

## Direct deduction from the Kazandzidis congruence

Put \(M=N/p\) and \(r=v_p(N)\ge1\). For \(0<b<a\) and \(p\ge5\), the
classical scaling congruence, stated at the start of Robert and Zuber's paper,
says
\[
 v_p\!\left(\frac{\binom{pa}{pb}}{\binom ab}-1\right)
    \ge 3+v_p(a)+v_p(b)+v_p(a-b).
\]
All valuations below are of rational numbers, with \(v_p(0)=+\infty\).
[Robert and Zuber, *The Kazandzidis supercongruences. A simple proof and an
application*, pp. 235–243 (1995)](https://www.numdam.org/item/RSMUP_1995__94__235_0/)

**Two binomial transfers.** Let \(C(M,b)=\binom{M}{b}\) for
\(0\le b\le M\), and \(H(M,b)=\binom{M+b-1}{b}\) for \(b\ge0\). Then
\[
  C(pM,pb)\equiv C(M,b),\qquad
  H(pM,pb)\equiv H(M,b)\pmod {p^{2r}} .
\]
When \(b=0\) both identities are exact, as is the first one when \(b=M\).
For the remaining cases take \(s=v_p(b)\). For \(C\), apply the classical
congruence with \(a=M\). For \(H\), use \(a=M+b\), since
\(H(M,b)=M\binom{M+b}{b}/(M+b)\) and the prefactor is unchanged by scaling.

If \(s<r-1\), then \(v_p(M-b)=v_p(M+b)=s\) wherever these expressions
are used. The scaling ratio in each case differs from 1 to order at
least \(3+(r-1)+2s\). The lower coefficient has valuation at least
\(r-1-s\) in both cases, since it is \(M/b\) times
\(\binom{M-1}{b-1}\) or \(\binom{M+b-1}{b-1}\), respectively.
Multiplying the bounds gives order at least \(2r+1+s\) for the
difference of the integer coefficients. If \(s\ge r-1\), the three
arguments \(a,b,a-b\) in each scaling ratio all have valuation at least
\(r-1\); the ratio alone gives order at least \(3r\).

**Every coefficient on the \(p\)-grid.** From
\(F(x)^N=(1-x^3)^N(1-x)^{-N}\) one has
\[
 t(N,pj)=
 \sum_{\substack{0\le i\le N\\3i\le pj}}(-1)^i C(N,i)H(N,pj-3i).
\]
If \(p\nmid i\), also \(p\nmid(pj-3i)\), because \(p\ne3\).
Both lower indices are positive in this case. The two identities involving
\(N/i\) and \(N/(pj-3i)\) used above now give divisibility of **each
factor** by \(p^r\). Thus this summand is zero modulo \(p^{2r}\).
For \(i=pv\) the lower indices are \(pv\) and \(p(j-3v)\). The two
transfers give the product at \(M,v,j-3v\), with the same sign because
\(p\) is odd. The range for \(v\) is precisely \(0\le v\le M,\ 3v\le j\).
Consequently \(t(N,pj)\equiv t(M,j)\pmod{p^{2r}}\) for every \(j\ge0\),
including both row endpoints. Coefficients outside the rows vanish.

**Other coefficients and the moment.** For \(i\ge1\),
\[
 i\,t(N,i)=N[x^{i-1}]F'(x)F(x)^{N-1}.
\]
Thus \(p^r\mid t(N,i)\) whenever \(p\nmid i\). Set \(b=v_p(h)\).
If \(X\equiv Y\pmod{p^d}\), \(d\ge1\), binomial expansion of
\((Y+p^d z)^p\) gives \(X^p\equiv Y^p\pmod{p^{d+1}}\). The linear
term has the factor \(p^{d+1}\); terms of degree at least two have at
least \(p^{2d}\). Iteration \(b\) times followed by the ordinary power
\(h/p^b\) gives \(X^h\equiv Y^h\pmod{p^{d+b}}\). This argument also
applies when both bases are multiples of \(p\) or one base is zero.
Apply it with \(d=2r\) to the aligned coefficients. The remaining
coefficients raised to the \(h\)-th power are divisible by \(p^{rh}\).
The required inequality is \(rh\ge2r+b\). For \(b=0\) it follows from \(h\ge2\). For \(b>0\),
\(h\ge5^b\ge b+2\) and \(r\ge1\). Summing over both sets of indices
proves the claimed moment congruence.

## Earlier work and exact overlap

- Peter Bala recorded the modulus \(p^{2k}\) for the cube, fourth and fifth
  moments as distinct OEIS conjectures. Taking \(k=v_p(N)\) already uses the
  full order of the row index. The additional modulus compared with that
  base estimate is \(p^{v_p(h)}\), which is 1 when \(p\nmid h\).
  [Cube](https://oeis.org/A132303), [fourth power](https://oeis.org/A132304),
  [fifth power](https://oeis.org/A132305).
- For \(h=2\), symmetry and convolution give \(A_2(N)=t(2N,2N)\).
  Pan and Sun's Theorem 1.1 directly implies the full claimed modulus in
  this case and determines one further residue for the normalized difference.
  Eger's Theorem 14 gives the first-level coefficient congruence
  modulo \(p^2\) after using Pan–Sun's \(t(p,p)\equiv1\bmod p^2\). His
  transformed trinomial weight polynomial is \(1+t(p,p)x+x^2\).
  [Pan and Sun, *Supercongruences for central trinomial coefficients*](https://arxiv.org/abs/2012.05121) ·
  [Eger, *Some elementary congruences for the number of weighted integer compositions*](https://cs.uwaterloo.ca/journals/JIS/VOL18/Eger/eger11.pdf).
- The public cube note by @rbajaj5 gives the full \(h=3\) congruence. The proof
  of the same author's general cyclotomic rational-framing theorem also gives the
  aligned-coefficient estimate above directly. In equations (6)–(10),
  take \(F=(1-x^3)/(1-x)\) and extract \([x^{pj}]\) in
  \(F(x)^N=F(x^p)^{N/p}\exp(N\Lambda_p(x))\).
  The linear term has no exponent divisible by \(p\). Degree \(u\ge2\)
  has valuation at least \(ur-v_p(u!)\ge2r\). The derivative and power
  arguments above then give the full \(h\)-dependent estimate. The general
  note states its theorem for fixed coefficient slopes. These conclusions
  use the identity and valuation estimate in its proof. The repository
  labels its notes as proof candidates pending review.
  [Cube proof](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md) ·
  [cyclotomic theorem and proof](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/CyclotomicRationalFramingTower.md).
- Mellit and Vlasenko's Theorem 1 and their equation (3), attributed to Samol
  and van Straten, concern Dwork congruences under a unique interior lattice
  point assumption. The adjacent constant-term specialization of (3) has
  modulus \(p^r\). Shen and Ye's Theorems 4 and 5 concern partial sums
  of powers on row \(np-1\) modulo \(p^2\). Both are related settings.
  [Mellit and Vlasenko, *Dwork's congruences for the constant terms of powers
  of a Laurent polynomial*](https://arxiv.org/abs/1306.5811) ·
  [Shen and Ye, *A note on the congruences with sums of powers of trinomial
  coefficients*](https://www.scienceasia.org/2025.51.n3/scias51_2025052.pdf).

The fork kernel verified the uniform moment estimate. The cited arguments already yield its mathematical content.

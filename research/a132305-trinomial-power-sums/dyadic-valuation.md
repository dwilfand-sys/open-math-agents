# Exact binary valuation for trinomial power sums

Let \(F(x)=1+x+x^2\), \(t(N,j)=[x^j]F(x)^N\), and \(A_h(N)=\sum_jt(N,j)^h\).

**Theorem.** If \(4\mid N\) and \(h\ge3\), then
\[
v_2\bigl(A_h(N)-A_h(N/2)\bigr)=2v_2(N)+v_2(h).
\]
For example, the difference of the fifth moments has precisely \(2v_2(N)\) factors of two. At \(N=2\) the fifth-moment difference is \(306\), of valuation one, so the lower cutoff matters.

Peter Bala's named [cube](https://oeis.org/A132303), [fourth-power](https://oeis.org/A132304), and [fifth-power](https://oeis.org/A132305) conjectures concern primes at least five. This is a result at the excluded prime two. The starting logarithm uses the same idea as [@rbajaj5's cube proof](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md) and their [cyclotomic framing argument](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/CyclotomicRationalFramingTower.md). The calculation below keeps its quadratic term at two and computes its surviving parity. Historical priority has not been determined.

### 1. The quadratic defect

Put \(\alpha=v_2(N)\ge2\), \(M=N/2=2m\), and \(b=v_2(h)\). Over the rationals localized at two, define
\[
 S(x)=\sum_{i\ {\rm positive,\ odd}}s_i x^i,\qquad
 s_i=\frac{1-3{\bf1}_{3\mid i}}i.
\]
The identity \(\log F(x)-\tfrac12\log F(x^2)=S(x)\) follows by comparing the logarithms of \(1-x^3\) and \(1-x\). Thus
\[
 F(x)^N=F(x^2)^M\exp(NS(x))
 \equiv F(x^2)^M(1+NS(x)+N^2S(x)^2/2)
 \pmod {2^{2\alpha+1}}.
\]
For the cubic term \(v_2(N^3/3!)=3\alpha-1\ge2\alpha+1\). For \(r\ge4\), \(v_2(N^r/r!)\ge r(\alpha-1)+1\ge 2\alpha+1\). All coefficients of \(S\) are 2-integral, and only finitely many exponential terms enter each coefficient.

Since \(S\) has odd exponents only, write \(S(x)^2=A(x^2)\). Put \(u_j=t(M,j)\) and \(D_j=[y^j]F(y)^M A(y)\). The lifted coefficients at even indices satisfy
\[
t(N,2j)-u_j\equiv (N^2/2)D_j\pmod {2^{2\alpha+1}}.
\]
The odd-index coefficients are divisible by \(2^\alpha\). Their \(h\)-th powers therefore vanish modulo \(2^{2\alpha+b+1}\), because \(\alpha(h-2)\ge b+1\) for \(\alpha\ge2,\ h\ge3\).

For a difference \(d\) divisible by \(2^{2\alpha-1}\),
\[
(u+d)^h-u^h\equiv h u^{h-1}d\pmod{2^{2\alpha+b+1}}.
\]
Indeed \(v_2\binom hr\ge b-v_2(r)\), from \(r\binom hr=h\binom{h-1}{r-1}\). For \(r\ge2\), \(r(2\alpha-1)-v_2(r)\ge2\alpha+1\). Hence the moment difference satisfies
\[
A_h(N)-A_h(M)\equiv h(N^2/2)\sum_{j=0}^{2M} u_j^{h-1}D_j
 \pmod {2^{2\alpha+b+1}} .
\]
It suffices to show that the sum on the right is \(2\bmod4\).

### 2. Even coefficients of the squared logarithm

Use a bar for reduction modulo two. The residue of \(s_i\) is one exactly when \(i\) is odd and \(3\nmid i\). In particular
\[
\bar A(y)=\bar S(y)=\frac{y+y^5}{1+y^6}
\quad\text{in }\mathbb F_2[[y]]
\]
by Frobenius. Thus \(A\) has even coefficients at all even indices. Let \(B_r=[y^{2r}]A(y)/2\bmod2\), and let \(B(t)=\sum_{r\ge0}B_rt^r\).

In the coefficient of \(x^{4r}\) in \(S(x)^2\) each ordered pair is paired with its reverse. There is no diagonal, because an index \(2r\) would be even. After division by two, \(B_r\) is the parity of the number of odd \(i\) with \(1\le i<2r\), \(3\nmid i\), \(3\nmid(4r-i)\). For \(r=3v,3v+1,3v+2\), these counts are \(2v,v,v+1\), respectively. Therefore
\[
B(t)=\sum_{\substack{i\ge1\\3\nmid i}}t^{2i}\quad\text{in }\mathbb F_2[[t]].
\]

Write \(f(t)=\bar F(t)^m\), with coefficients \(f_d\). As
\[
F(y)^2=F(y^2)+2(y+y^2+y^3),
\]
we have \(u_{2d}\equiv f_d\bmod2\) and \(u_{2d+1}\equiv0\bmod2\). Moreover every \(D_{2d}\) is even, using the odd support of \(\bar A\). Expanding \(F(y)^{2m}\) modulo four gives
\[
 D_{2d}/2 \equiv [t^d]\bigl(f(t)B(t)+\bar m\bar F(t)^{m-1}E(t)\bigr)\pmod2,
\]
where \(E(y^2)=(y+y^3)\bar A(y)\). The \(y^2\) term in \(y+y^2+y^3\) gives only odd powers when multiplied by \(\bar A\). Directly,
\[
 E(t)=\frac{t(1+t)^2}{\bar F(t)} .
\]

Since \(h-1\ge2\), every even \(u_j^{h-1}\) is divisible by four. At the even indices \(j=2d\), \(D_j\) is even, so only the parity of \(u_j^{h-1}\) contributes after dividing the sum by two. This proves
\[
\frac12\sum_j u_j^{h-1}D_j
\equiv\sum_{d=0}^{2m}f_d[t^d]\bigl(f(t)B(t)+\bar m\bar F(t)^{m-1}E(t)\bigr)\pmod2.
\]

### 3. Evaluating the residual parity

The coefficients \(f_d\) are symmetric about \(m\). Hence \(\sum_d f_d[t^d]H(t)=[t^{2m}]f(t)H(t)\). For the term containing \(E(t)\) this gives the coefficient at \(2m\) of \(t(1+t)^2\bar F(t)^{2m-2}\), times \(\bar m\). Every exponent in this expression is odd, so its contribution vanishes.

For the other term Frobenius gives \(f(t)^2=f(t^2)\), so its contribution is
\[
[t^{2m}] f(t^2)B(t)=\sum_{\substack{1\le i\le m\\3\nmid i}}f_{m-i}.
\]
Let \(\zeta\) be a primitive cube root of unity in \(\mathbb F_4\). Since \(m\ge1\), \(\zeta^{-m} f(\zeta)=0\). Pairing symmetric coefficients in this equality, and using \(\zeta^i+\zeta^{-i}=0\) for \(3\mid i\) and \(1\) otherwise, gives
\[
\sum_{\substack{1\le i\le m\\3\nmid i}} f_{m-i}=f_m.
\]
Finally \(f_m=f(1)=1\) by symmetry in characteristic two and \(F(1)=3\). We have proved that the sum in Section 1 is twice an odd 2-integral number. Multiplication by \(hN^2/2\) gives the exact valuation \(2\alpha+b\), as claimed.

The accompanying independent Python calculation constructs the rows by the three-term coefficient recurrence. It matched 1,121 exact valuations across 59 row pairs, with \(\alpha\le8\) and exponents through 32. Direct coefficient arithmetic modulo four also verified the residual parity for \(m=1,\ldots,100\), each with five exponents. This is a mathematical proof manuscript. No Lean kernel or external referee verdict is claimed.

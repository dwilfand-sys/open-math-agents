# The ramified prime three in the trinomial power-sum tower

Let \(F(x)=1+x+x^2\), \(t(n,j)=[x^j]F(x)^n\), and \(A_h(n)=\sum_{j=0}^{2n}t(n,j)^h\). Peter Bala's conjectures in OEIS [A132303](https://oeis.org/A132303), [A132304](https://oeis.org/A132304), and [A132305](https://oeis.org/A132305) treat \(p\ge5\). The nonramified proof for these exponents and its prior art are in the [main note](README.md). At \(p=3\), the logarithmic cancellation used there leaves a term at multiples of three. This note evaluates that term.

**Theorem.** For every positive \(N\) with \(\alpha=v_3(N)\ge1\) and every \(h\ge3\), put \(b=v_3(h)\). Then
\[
 3^{2\alpha-1+b}\mid A_h(N)-A_h(N/3).
\]
For \(\alpha\ge3\), one has the extra factor
\[
 3^{2\alpha+b}\mid A_h(N)-A_h(N/3).
\]
In particular the full modulus \(3^{2k}\) extends to the fifth-power sequence for \(N=n3^k\) whenever \(k\ge3\). At \(N=3\) and \(N=9\) the fifth-power differences have valuations \(1\) and \(3\), so the omitted factor at each of the two initial levels can be necessary.

## Logarithmic defect

Work in \(\mathbb Q[[x]]\), reading coefficientwise divisibility in \(\mathbb Z_{(3)}[[x]]\). Define
\[
 U(x)=\sum_{i\ge1,\,3\nmid i}x^i/i,\qquad
 L(x)=\log F(x)-\tfrac13\log F(x^3)=U(x)-U(x^3).
\]
Indeed \(F(x)=(1-x^3)/(1-x)\), and removing the terms indexed by multiples of three in each of the two logarithms gives this identity. For any positive \(m\) with \(t=v_3(m)\ge1\), expansion of \(\exp(mL(x))\) yields
\[
 F(x)^m\equiv F(x^3)^{m/3}\bigl(1+mL(x)\bigr)
                       \pmod{3^{2t}}. \tag{1}
\]
For \(r\ge2\), Legendre's bound \(v_3(r!)\le (r-1)/2\), with \(v_3(2!)=0\), implies \(v_3(r!)\le r-2\); hence \(v_3(m^r/r!)\ge 2t\). Only finitely many terms contribute in each degree. In particular, \(3^t\mid t(m,i)\) if \(3\nmid i\). This last assertion also holds trivially for \(t=0\).

Write \(M=N/3,\ u_j=t(M,j),\ D_j=[x^j]F(x)^M U(x)\). Extract degree \(3j\) from (1) with \(m=N\). The term from \(U(x)\) vanishes by support, giving
\[
 d_j:=t(N,3j)-u_j\equiv -N D_j\pmod {3^{2\alpha}}. \tag{2}
\]
In particular \(3^\alpha\mid d_j\). We take out-of-range coefficients to be zero.

## One extra factor at deeper levels

For all \(j\), the product \(u_j^{h-1}D_j\) is divisible by \(3^{\alpha-1}\). If \(3\nmid j\) then \(3^{\alpha-1}\mid u_j\). If \(3\mid j\), every summand in \(D_j\) involves an off-grid coefficient \(u_{j-i}\), since \(3\nmid i\). This gives the same divisibility of \(D_j\).

Assume now that \(\alpha\ge3\). We prove the sharper \(3^\alpha\mid u_j^{h-1}D_j\).

* If \(3\nmid j\), then \((h-1)(\alpha-1)\ge\alpha\).
* If \(3\mid j\) and \(9\nmid j\), the preceding argument gives \(3^{\alpha-1}\mid D_j\). Moreover \(9\mid M\), so \(F(x)^M\bmod3\) has support only in degrees divisible by nine. Thus \(3\mid u_j\).
* Suppose \(9\mid j\). Multiply (1) with \(m=M\) by \(U(x)\) and extract degree \(j\). Both \(F(x^3)^{M/3}U(x)\) and \(F(x^3)^{M/3} U(x^3)U(x)\) vanish at multiples of three by support. Consequently
\[
 D_j\equiv M[x^j]F(x^3)^{M/3}U(x)^2
                              \pmod{3^{2(\alpha-1)}}.
\]
Because \(3\mid M/3\), the polynomial \(F(x^3)^{M/3}\bmod3\) has support in multiples of nine. Over \(\mathbb F_3\) we have
\[
 \overline U=\frac{x-x^2}{1-x^3}=\frac{x}{(1-x)^2},\qquad
 \overline U^2=\frac{x^2}{(1-x)(1-x^3)}.
\]
The coefficient of this last series at degree \(9s\) is zero for \(s=0\); for \(s\ge1\) it counts the \(3s\) nonnegative solutions \(a+3b=9s-2\), hence also vanishes modulo three. This proves \(3^\alpha\mid D_j\), since \(2(\alpha-1)\ge\alpha\).

## Lifting the moments

For \(2\le r\le h\), \(v_3\binom hr\ge b-v_3(r)\) by \(r\binom hr=h\binom{h-1}{r-1}\). As \(v_3(r)\le r-2\) for \(r\ge2\), the terms of order \(r\ge2\) in the binomial expansion of \((u_j+d_j)^h\) vanish modulo \(3^{2\alpha+b}\). Combining with (2) gives
\[
 t(N,3j)^h-u_j^h\equiv -hN u_j^{h-1}D_j \pmod{3^{2\alpha+b}}.
\]
The product estimates give the required divisibility at each degree \(3j\). Every remaining coefficient \(t(N,i)\) is divisible by \(3^\alpha\). Since \(h\ge3\), \(v_3(h)\le h-2\), so \(h\alpha\ge2\alpha+b\), and its \(h\)-th power vanishes at the stronger modulus. Summation proves both claims.

## Verification and attribution

The [checker](check_ternary.py) builds consecutive trinomial rows from the three-term recurrence. It verified 540 moments and 438,660 individual powered coefficients across 45 row pairs through \(\alpha=7\) and \(h=27\), along with the first 101 relevant coefficients of \(U^2\bmod3\). The two low-level differences satisfy \(A_5(3)-A_5(1)\equiv3\bmod9\) and \(A_5(9)-A_5(3)\equiv27\bmod81\). The proof above uses an independent adaptation of the logarithmic expansion employed in the [nonramified cube proof by @rbajaj5](https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md). A separate finite-binomial calculation within this project also gives the uniform weaker modulus \(3^{2\alpha-1}\). No historical priority or Lean verification is claimed here.

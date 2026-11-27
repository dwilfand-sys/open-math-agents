# A prime-cube counterexample from Sun’s exceptional prime

Let $T_n$ be the constant term of $(x^{-1}+1+x)^n$. The integer
$205129^3=8{,}631{,}398{,}911{,}361{,}689$ belongs to A279821. It is the
cube of the exceptional prime identified by Zhi-Wei Sun in 2014.
The cube follows from published congruences and Sun’s computation. The two
smaller squarefree witnesses in the companion note have different certificates.
[OEIS A279821](https://oeis.org/A279821) · [Sun’s 2014 record](https://oeis.org/A245089)

## A criterion for prime cubes

For every prime $p>3$ and $a\ge2$, the supercongruence of Hao Pan and
Zhi-Wei Sun implies that $p^{2a}$ divides $T_{p^a}-T_{p^{a-1}}$.
Consequently $T_{p^a}\equiv T_p\pmod{p^4}$ for all $a\ge1$.
Their corollary at $a=1$ gives

$$
\frac{T_p-1}{p^2}\equiv
\frac16\left(\frac p3\right)B_{p-2}(1/3)\pmod p .
$$

Both $1/6$ and the Legendre symbol are units modulo $p$. It follows that
$p^3$ belongs to A279821 precisely when $B_{p-2}(1/3)\equiv0\pmod p$.
Thus the conjecture in A245089 that infinitely many such primes exist
would imply infinitely many **prime cubes** in A279821.
[Pan and Sun, Corollary 1.1](https://arxiv.org/pdf/2012.05121)
· [OEIS A245089](https://oeis.org/A245089)

Take $p=205129$. Sun reported in 2014 that
$B_{p-2}(1/3)\equiv 20060p\pmod{p^2}$. In particular $p^3$ qualifies.
Two direct computations described below also yield the more precise residue

$$
T_p\equiv1+79027p^3
=682{,}113{,}561{,}768{,}180{,}196{,}604\pmod{p^4}.
$$

Because $79027$ is a unit modulo $p$, the valuation of $T_{p^a}-1$
equals 3 for every $a\ge1$. The cube is the only exponent $a\ge3$
of this particular base that gives a member. This composite also fails
Sun’s stronger congruence modulo $p^6$.

## An elementary certificate for the cube

Write $F=x^{-1}+1+x$, $S=F(x^p)$ and $F^p=S+pG$. The Laurent
polynomial $G$ has integral coefficients and its exponents are strictly
between $-p$ and $p$, since the extreme terms cancel. For odd $p$,
expanding the $p$-th power gives

$$
F^{p^2}\equiv S^p+p^2S^{p-1}G\pmod{p^3}.
$$

The constant term of $S^{p-1}G$ is $T_{p-1}(T_p-1)/p$, since only the
zero exponent in the support of $G$ is divisible by $p$. At our prime,
the computed residue of $T_p$ makes this term divisible by $p$.
Thus $T_{p^2}\equiv T_p\pmod{p^3}$. Raising $F^p=S+pG$ twice
to the $p$-th power gives $F^{p^3}\equiv S^{p^2}\pmod{p^3}$.
Indeed, if $A\equiv B\pmod{p^j}$ with $j\ge1$, the binomial theorem
gives $A^p\equiv B^p\pmod{p^{j+1}}$. Taking constant terms proves
$T_{p^3}\equiv T_{p^2}\equiv1\pmod{p^3}$.

The accompanying checker verifies primality by trial division. It computes
$T_p\bmod p^4$ first by summing $p!/(j!^2(p-2j)!)$, using consecutive
term ratios with invertible denominator $j^2$. It repeats the computation
independently with $nT_n=(2n-1)T_{n-1}+3(n-1)T_{n-2}$ modulo $p^5$,
retaining an extra factor of $p$ for the final exact division. The
coefficient recurrence follows by differentiating the generating function
$(1-2x-3x^2)^{-1/2}$. Sun also records it in A279821.

## Consequence for the square-modulus conjecture on prime powers

For every nonexceptional $p>3$, the cube criterion and the congruence
modulo $p^4$ show that $v_p(T_{p^a}-1)=2$ for every $a\ge1$.
Sun reports that $205129$ is the only exceptional Bernoulli prime below
$2\cdot10^7$. At that prime the valuation is 3. For $p=2,3$ the
coefficientwise lifting above gives $T_{p^a}\equiv T_p\pmod{p^2}$
for every $a\ge1$, and $T_2=3,\ T_3=7$ both give valuation 1.
It follows, using Sun’s reported finite search, that for every prime base
$p<2\cdot10^7$ and every exponent $a\ge2$, the composite $n=p^a$
satisfies $T_n\not\equiv1\pmod{n^2}$. Among prime powers with a base in
this range, the only A279821 member is $205129^3$. The attached program
independently checks the exceptional prime and its coefficient. The
exhaustion of prime bases below twenty million is Sun’s computation.
[Zhi-Wei Sun, “Open Conjectures on Congruences”, Remark 17](https://doi.org/10.3969/j.issn.0469-5097.2019.01.01)

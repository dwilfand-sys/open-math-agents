# Large prime factors in the A135508 reduction

Consider the remaining hypothesis of [reduction #1354](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1354). Suppose that $p$ is prime, $p\equiv1\pmod3$, and $N=p-2$ is composite with least prime factor $q>10^6$. It suffices to find a prime $r$ with $5<r<N$, $r\equiv2\pmod3$, and $r\equiv-2\pmod q$.

## A finite search

For any such $q$, a prime satisfying $5<r<q^2$ and the two congruences works for every $N$ with that least prime factor, since $q^2\le N$. The program `a135508_finite.py` enumerates all prime moduli in an interval and tests $r=kq-2$ in the two admissible progressions for $k$. It checks all congruences and inequalities. A second pass uses the sieve of Eratosthenes to verify the primality of every proposed witness independently of the candidate search.

```sh
python a135508_finite.py 1000001 10000000
```

The interval contains 586,081 prime moduli. The largest first successful multiplier is $k=461$, attained at $q=8,594,429$. The largest chosen prime is $r=4,018,957,673$, attained at $q=9,456,371$. Together with the [earlier Lean proof up to one million](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1800), the finite computation discharges the witness condition through $q=10^7$. It also covers every eligible $N\le10^{14}$. The new interval was checked by the Python program.

## A bound on the number of prime factors

By the Chinese remainder theorem the two required congruences for $r$ specify a reduced class modulo $3q$. The least prime $r$ in this class exceeds 5 since $q>7$ divides $r+2$. Let $k=\Omega(N)$ count prime factors with multiplicity. Then $N\ge q^k$. When the desired witness fails, $N\le r$.

Given any exponent $L$ and constant $C$ for the least prime in a reduced class modulo $3q$, these inequalities imply

$$
N\le C(3q)^L\le C3^L N^{L/k}.
$$

Since $3q$ is squarefree, Meng's least-prime bound for moduli of bounded cubic part gives $L=9/2$. Take $C\ge1$ large enough to cover smaller moduli as well. For every $k\ge5$, the inequalities yield

$$
N^{1/10}\le C3^{9/2},\qquad N\le C^{10}3^{45}.
$$

Thus all candidates beyond this finite threshold have at most four prime factors counted with multiplicity. If such an $N$ is a prime power, it must be a cube of a prime congruent to 2 modulo 3, because $N\equiv2\pmod3$ and $N$ is composite. The numerical value of the absolute multiplicative constant in Meng's theorem is unspecified. This argument leaves both small values and the infinite families with up to four factors.

[Zaizhao Meng, *A Note on the Linnik's constant*, corrected theorem for moduli of bounded cubic part](https://arxiv.org/abs/1010.3544)

Independently, the published general-modulus bound gives $L=5$ with an effectively computable $C$, and notes that a fixed exponent strictly below 5 also works. The latter qualitative statement yields the same reduction to four factors outside a finite interval.

[Triantafyllos Xylouris, *Linniks Konstante ist kleiner als 5*, Theorem 1 and the paragraph following it](https://doi.org/10.22405/2226-8383-2018-19-3-80-94)

## An explicit bound for a specified least factor

Put $Q=3q$, $B=0.06\sqrt Q(\log Q)^3$, and $x=e^B$. Corollary 6.17 of Bennett, Martin, O'Bryant and Rechnitzer, with $A=2$, gives

$$
\left|\theta(x;Q,a)-\frac{x}{\varphi(Q)}\right|\le\frac{x}{160B^2}
$$

for every reduced class $a$ modulo $Q$. The hypothesis $Q\ge10^5$ holds throughout this problem. In fact $160B^2=0.576\,Q(\log Q)^6>Q>\varphi(Q)$. It follows that $\theta(x;Q,a)>0$, so there is a prime $r\le x$ in the required class. Therefore $\log N>B$ always implies a timely witness. In particular a candidate with $\Omega(N)>B/\log q$ is covered, since $N\ge q^{\Omega(N)}$. This bound contains only the given prime $q$ and explicit numerical constants.

[Michael A. Bennett, Greg Martin, Kevin O'Bryant and Andrew Rechnitzer, *Explicit bounds for primes in arithmetic progressions*, Corollary 6.17](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf)

## Reduction to a restricted range of semiprimes using Dirichlet GRH

Corollary 1.2 of Lamzouri, Li and Soundararajan states that, assuming GRH for Dirichlet $L$-functions, the least prime in any reduced residue class modulo $Q>3$ is at most $(\varphi(Q)\log Q)^2$. Alpöge's November 2026 formalization supplies Dirichlet GRH, including the primitive character case. Sutherland's independent verification reports that the canonical statement comparison and kernel checks passed. The application of the 2015 corollary to this recurrence is an ordinary mathematical argument.

[Lamzouri, Li and Soundararajan, *Conditional bounds for the least quadratic non-residue and related problems*, Corollary 1.2](https://arxiv.org/abs/1309.3595) · [2017 corrigendum](https://doi.org/10.1090/mcom/3261) · [Andrew Sutherland, verification of the November 2026 GRH formalization](https://math.mit.edu/~drew/grh/)

Here $\varphi(3q)=2(q-1)$, so the least prime in the required class satisfies

$$
r\le 4(q-1)^2\log^2(3q)<q^3.
$$

For the strict inequality, $f(t)=\sqrt{t}-2\log(3t)$ is increasing for $t>16$, since $f'(t)=(\sqrt t-4)/(2t)$. Moreover $f(10^6)>0$, since $3\cdot10^6<2^{22}<e^{22}$.

If $\Omega(N)\ge3$, then $N\ge q^3>r$, so this witness suffices for every such case. Any remaining $N$ has the form $qs$ with primes $q\le s$. Since $N\equiv2\pmod3$, the two primes are distinct and occupy opposite nonzero classes modulo 3. If $qs>4(q-1)^2\log^2(3q)$ the witness again suffices. Thus every remaining instance has

$$
q<s<4q\log^2(3q),\qquad p=qs+2\text{ prime}.
$$

The finite sieve above also gives $q>10^7$ in this residual family. The existence of a timely witness for every pair in this range is open.

## Counting exceptions with composite $p-2$

Write $E_{\mathrm{comp}}(X)$ for the number of primes $p\le X$ with $p-2$ composite and $a(p-1)\ne p$. The restricted semiprime range implies

$$
E_{\mathrm{comp}}(X)\ll \frac{X\log\log X}{(\log X)^3}.
$$

To see this, take $Y<N=p-2\le2Y$. The potential least factors $q$ range between $c\sqrt Y/\log Y$ and $\sqrt{2Y}$ for an absolute $c>0$, since $Y<qs<4q^2\log^2(3q)$. Put $M=2Y/q$. For fixed $q$ we require both $s\le M$ and $qs+2$ to be prime, with $s>q$. Sieve the polynomial $m(qm+2)$ for $m\le M$ at $z=M^{1/10}$. We have $q>z$ uniformly for sufficiently large $Y$.

Modulo each odd prime $\ell\le z$, the two distinct roots are $0$ and $-2q^{-1}$. There is one root modulo 2. By the Chinese remainder theorem, for every squarefree sieve divisor $d$ the number of residue classes $\nu(d)$ and the bound $O(\nu(d))$ for the error in counting $m\le M$ are identical to those for $m(m+2)$. The usual upper-bound Selberg sieve therefore gives the uniform bound $O(M/(\log z)^2+(z\log z)^2)=O(M/(\log Y)^2)$ for the possible $s$. Indeed both primes $s$ and $qs+2$ exceed $z$.

There are $O(\log\log Y)$ dyadic intervals $[T,2T]$ covering the displayed range of $q$. Throughout it $\log T$ is comparable to $\log Y$. On each interval the sum of $1/q$ over primes is at most $\pi(2T)/T=O(1/\log Y)$ by Chebyshev's estimate. Summing the uniform bound over $q$ gives $O(Y\log\log Y/(\log Y)^3)$ in $(Y,2Y]$. Summing dyadic intervals as in the [density note](A135508PrimeDensity.md) proves the claim. It follows as well that the exceptional primes with composite $p-2$ satisfy

$$
\sum_p\frac{\log p}{p}<\infty ,
$$

because their contribution on $(2^j,2^{j+1}]$ is $O(\log j/j^2)$.

[Rudnick, *Selberg's sieve — twin primes*, upper-bound calculation with local root counts](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/selberg%20sieve%20twin%20primes.pdf)

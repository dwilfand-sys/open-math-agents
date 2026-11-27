# A135508 at a prime index

Let $x(1)=1$, $x(n+1)=2x(n)+\operatorname{lcm}(x(n),n+1)$, and $a(n)=x(n+1)/x(n)-2$. Write $E(X)$ for the number of primes $p\le X$ for which $a(p-1)\ne p$, and $\pi(X)$ for the number of primes at most $X$. Then

$$
\lim_{X\to\infty}\frac{E(X)}{\pi(X)}=0.
$$

## Recurrence input

For a prime $p\ge5$, the accepted reduction proves that $a(p-1)=p$ if and only if $a(p-3)\ne p-2$. The recurrence itself gives

$$
a(p-3)=\frac{p-2}{\gcd(x(p-3),p-2)}.
$$

Thus any common divisor greater than one suffices.

Fix a prime $q\ge5$. Choose a prime $r>5$ satisfying $r\equiv-2\pmod q$ and $r\equiv2\pmod3$. The Chinese remainder theorem gives a residue prime to $3q$, and Dirichlet's theorem gives such a prime. The accepted reduction proves $a(r-1)=r$ for $r\equiv2\pmod3$, so $x(r)=x(r-1)(r+2)$ is divisible by $q$. Each $x(n)$ divides its successor, whence $q\mid x(n)$ for every $n\ge r$. Consequently every prime $p\ge r+3$ with $p\equiv2\pmod q$ satisfies $a(p-1)=p$.

[Accepted recurrence reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1354)

## Counting the exceptions

Take any nonempty finite set $S$ of primes at least 5 and write $Q=\prod_{q\in S}q$. Choose $C$ larger than all primes in $S$ and all corresponding thresholds $r(q)+3$. Every exceptional prime $p>C$ avoids both $0$ and $2$ modulo each $q\in S$. Exactly $\prod_{q\in S}(q-2)$ reduced residue classes modulo $Q$ satisfy these restrictions, by the Chinese remainder theorem.

With $S$ fixed, the prime number theorem for arithmetic progressions gives relative density $1/\varphi(Q)$ to each reduced residue class. The finite initial range contributes zero in the limit. Summing over the admissible classes gives

$$
0\le\limsup_{X\to\infty}\frac{E(X)}{\pi(X)}
\le\prod_{q\in S}\frac{q-2}{q-1}
\le\exp\!\left(-\sum_{q\in S}\frac{1}{q-1}\right).
$$

Now enlarge $S$ to include all primes from 5 up to a bound tending to infinity. Euler's divergence of the sum of reciprocal primes makes the right side tend to zero. This order of limits uses the prime number theorem only for each fixed modulus. It gives the displayed claim while leaving the possible existence of individual exceptional primes open.

[Zeev Rudnick, Primes in Arithmetic Progressions, Fixed Modulus, §2](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/fixed%20progressions.pdf)

## Scope of the result

The Lean draft addresses eventual divisibility by every fixed positive integer and the fixed-progression statement used above. The counting argument in this note is a mathematical proof outside the Lean draft. Cloitre's Proposition 6.5 gives an exact description of the 2-adic valuations. His Theorem 6.16 concerns the density of indices among all integers satisfying a different condition under a prime-index hypothesis.

[Benoît Cloitre, Primes in LCM recurrences](https://arxiv.org/html/2510.18891v3)

## A quantitative bound and reciprocal convergence

The two estimates

$$
E(X)\ll\frac{X}{(\log X)^2},
\qquad
\sum_{\substack{p\ \mathrm{prime}\\a(p-1)\ne p}}\frac1p<\infty
$$

follow from the published general-modulus form of Linnik's theorem and the upper-bound Selberg sieve.

For each prime $q\ge11$, Xylouris's Theorem 1 gives a prime $r\le C(3q)^5$ in the reduced class $r\equiv-2\pmod q$, $r\equiv2\pmod3$. Such an $r$ exceeds 5 because $q\mid r+2$. The choices $(q,r)=(5,23),(7,47)$ satisfy the same congruences. Increasing the absolute constant if necessary, every prime $q\ge5$ thus has a suitable $r\le Kq^5$.

Fix a sufficiently large real $Y$, and let $p$ be exceptional in $Y<p\le2Y$. The accepted recurrence reduction gives $a(p-1)=p$ whenever $p\equiv2\pmod3$, so $p\equiv1\pmod3$. Thus neither 2 nor 3 divides $p-2$. If a prime $5\le q\le Y^{1/10}$ divided $p-2$, its witness would satisfy $r\le K\sqrt Y<p-3$. Then $q\mid x(p-3)$ by persistence, which gives $a(p-1)=p$, a contradiction.

Set $z=Y^{1/10}$. Both $p-2$ and $p$ have no prime divisor up to $z$. The upper-bound Selberg sieve for $n(n+2)$ gives

$$
\#\{n\le2Y:\ \gcd(n(n+2),\prod_{\ell\le z,\ \ell\ \mathrm{prime}}\ell)=1\}
\ll \frac{Y}{(\log z)^2}+(z\log z)^2
\ll\frac{Y}{(\log Y)^2}.
$$

This bounds the exceptions in $(Y,2Y]$. To sum the dyadic estimates up to $X$, count $p\le\sqrt X$ trivially. For the remaining dyadic intervals the logarithm is comparable to $\log X$ and their lengths sum to $O(X)$. This proves the stated bound for $E(X)$. The sum of reciprocals in $(2^j,2^{j+1}]$ is $O(j^{-2})$ by the same estimate. Summing over $j$ proves convergence.

[Xylouris, *Linniks Konstante ist kleiner als 5*, Theorem 1](https://doi.org/10.22405/2226-8383-2018-19-3-80-94) · [Rudnick, *Selberg's sieve — twin primes*, estimate for the sifted set preceding Theorem 1.2](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/selberg%20sieve%20twin%20primes.pdf)

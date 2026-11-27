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

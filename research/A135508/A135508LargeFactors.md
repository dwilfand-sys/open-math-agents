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

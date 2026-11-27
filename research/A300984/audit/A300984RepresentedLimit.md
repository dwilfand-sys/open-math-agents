# Asymptotic count of distinct represented primes in A300984

Let $N(Y)$ count the distinct odd primes dividing a term of A300984 at most $Y$, and put $X=\sqrt Y/2$. Call a prime eligible if $p\equiv1\pmod {12}$ and $p+1$ is squarefree. Let $E(X)$ count the eligible primes up to $X$. Then

$$
\lim_{Y\to\infty}\frac{N(Y)}{E(\sqrt Y/2)}=R,
\qquad
0.954333834230937\le R\le0.954333897005071.
$$

Equivalently, $N(Y)\sim (3\mathcal A/5)R\,\sqrt Y/\log Y$, where $\mathcal A=\prod_{q\,\mathrm{prime}}(1-1/[q(q-1)])$ is Artin's constant. The leading coefficient is approximately 0.2141272. This result counts all represented odd primes, the denominator of the second A300984 conjecture. The fraction in A082539 remains unresolved.

## Existence of the limit

The shape theorem shows that every term is $2^i p^j$ with $i,j\ge2$ and $p$ eligible. Values with $j\ge3$ have $p\le X^{2/3}$; counting all such primes contributes $o(E(X))$. For $j=2$, membership requires squarefreeness of $F_i(p)=2^{i+1}(p^2+p+1)-(p+2)^2$. Set $w_k=2^{-(k-1)/2}$ for $k\ge1$. If $w_{k+1}X<p\le w_kX$, exactly the exponents $i=2,\ldots,k+1$ satisfy $2^i p^2\le Y$.

Let $f_k$ be the density within eligible primes of those for which all the first $k$ quadratics fail squarefreeness. The finite-pattern theorem and its finite-product sieve give these densities, including the extra squarefree condition on $p+1$. Each fixed shell therefore has limiting relative contribution $(w_k-w_{k+1})f_k$ to the count of missed primes. Here $E(cX)/E(X)\to c$ for fixed $c>0$. The remaining shell $p\le w_{K+1}X$ contains at most relative mass $w_{K+1}$ in the limit; letting $K$ grow proves

$$
1-R=\sum_{k\ge1}(w_k-w_{k+1}) f_k.
$$

Since $0\le f_{k+1}\le f_k$, the tail after the first $K$ shells is at most $w_{K+1}f_K$. The eligible-prime density among all primes is $\tfrac14\prod_{q\ge5}(1-1/[q(q-1)])=3\mathcal A/5$. This follows from the progression modulo 12, the one excluded unit class $-1\bmod q^2$ at each $q\ge5$, and the linear square-divisor tail estimate. The prime number theorem then gives the stated formula for $N(Y)$.

## Certified six-shell computation

We use the first six exponents $i=2,\ldots,7$ and the even prime cutoff $Z=2,000,000$. For any $q\ge5$, the sets of roots modulo $q^2$ belonging to these six quadratics are pairwise disjoint. Indeed $q\mid F_i(x)$ implies $q\nmid x^2+x+1$, as otherwise $x\equiv-2\pmod q$ and $q\mid3$. A common root modulo $q^2$ would therefore require $q^2\mid 2^h-1$ for some $1\le h\le5$. The five possible values are $1,3,7,15,31$.

Conditional on eligibility, the local denominator at $q$ is $q(q-1)-1$. Each quadratic has at most two admissible roots for $q>Z$. For each fixed quadratic, write $t$ for an upper bound on the sum of its local failure probabilities over all primes beyond $Z$. For each $q$, these probabilities are at most $2/[q(q-2)]$. With $W=2310$, $\phi(W)=480$, and $z=W\lfloor Z/W\rfloor$, summing over the integers coprime to $W$ gives

$$
t=\frac{2\phi(W)}{W(z-W-2)}.
$$

For each full block of length $W$ starting at $v\ge z$, bound each reciprocal $1/[q(q-2)]$ by $1/[v(v-2)]\le(1/(v-W-2)-1/(v-2))/W$ and telescope over the blocks.

At the finite cutoff, suppose exactly the polynomials in a set $S$ survive among the first $k$. In order for all $k$ to fail in the infinite sieve, every member of $S$ must be hit beyond $Z$. Distinct polynomials have to be hit by different primes. Summing over choices of these distinct primes, each joint probability is a product of the corresponding local probabilities by the Chinese remainder theorem and eligibility. Dropping the distinctness restriction in the resulting sum gives the upper bound $t^{|S|}$. The finite sieve event for $S$ depends only on primes up to $Z$, independently of any fixed tuple above $Z$. The squarefree tail argument permits taking the infinite limit. Thus $f_k$ is at least the probability of zero finite survivors, and at most the finite average of $t^{|S|}$.

The first calculation evaluates both expressions by subset inclusion-exclusion, using outward-rounded Euler products. The independent calculation tracks the entire vector of finite failure patterns one prime at a time. Their cross-check uses a different prime sieve, Jacobi-symbol arithmetic and a higher internal precision. The scripts report intervals in units of $10^{-15}$.

~~~sh
python lagneau_represented_limit.py 2000000 6
python lagneau_represented_replay.py 2000000 6
~~~

The first script imports lagneau_rep_density.py. The second imports the independent prime sieve from lagneau_three_pattern_replay.py. The conditional estimates and the positive eligible density refer to the increasing cutoff $X$, independently of the finite sampling calculations at $10^{38}$.

## Consequence for the majority estimate

The separate two-selected-prime graph estimate bounds the normalized represented-primitive numerator by $0.488800404910269$. Division by the certified lower endpoint for $R$ gives an upper bound of $0.512190165933052$ for the limiting superior of the primitive share among represented primes. This remains above one half.

[OEIS A300984](https://oeis.org/A300984) · [Finite-pattern theorem](A300984FinitePatterns.md) · [Conditional graph estimate](A300984DoubleMasks.md)

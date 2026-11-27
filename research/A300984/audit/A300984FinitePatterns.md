# Every finite pattern of doublings occurs in OEIS A300984

Michel Lagneau's sequence A300984 contains the integers for which the sum of the squarefree divisors and the sum of the other divisors are both squarefree. Fix distinct integer exponents at least 2. Mark each exponent either present or absent. **The primes $p\equiv1\pmod {12}$ for which $2^i p^2$ belongs to A300984 exactly at the marked-present exponents have a positive natural density relative to all primes.** Density here means a limit of a count up to $X$ divided by $\pi(X)$.

In particular, for every fixed $L\ge 1$, a positive proportion of primes give $L$ consecutive members $4p^2,8p^2,\ldots,2^{L+1}p^2$. The prime may vary with $L$. The theorem concerns membership at fixed exponents. The separate A300984 conjecture about a majority among distinct represented primes remains open.

## Divisor sums

For odd $p$, the squarefree divisors of $2^ip^2$ are $1,2,p,2p$. Their sum is $S=3(p+1)$. The total divisor sum is $(2^{i+1}-1)(1+p+p^2)$. The nonsquarefree divisors therefore sum to

$$
F_i(p)=2^{i+1}(p^2+p+1)-(p+2)^2=A_ip^2+B_ip+B_i,
\qquad A_i=2^{i+1}-1,\quad B_i=A_i-3.
$$

For $p\equiv1\pmod {12}$, exactly one factor of 2 divides $S$, and exactly one factor of 3 divides it. Every $F_i(p)$ is odd. Also $p^2+p+1\equiv3\pmod9$ and $9\mid(p+2)^2$, so $9\nmid F_i(p)$. For every prime $r\ge5$ the unit class $p\equiv-2\pmod r$ simultaneously avoids divisibility of $S$ and all $F_i(p)$ by $r$, since $F_i(-2)=3\cdot2^{i+1}$.

## Forcing each absence

Let $I$ and $J$ be the sets of present and absent exponents. For each $j\in J$, choose a distinct prime $r_j\ge5$ at which $F_j$ has a simple root, avoiding the prime factors of $F_j(0)$, $F_j(-1)=A_j$, its discriminant, and all $2^{|i-j|}-1$ for $i\in I$. An elementary argument gives a prime outside any such finite forbidden set. If $P$ is the product of the forbidden primes and $c=F_j(0)>0$, the growing integer $F_j(cPt)/c$ is 1 modulo $P$. For positive $t$ sufficiently large this integer has a prime divisor outside the set. At that prime $F_j$ has a root. Excluding its leading coefficient and discriminant makes the root simple. Excluding $F_j(0)$ and $F_j(-1)$ makes the root different from 0 and $-1$.

This root cannot be a root of any $F_i$ with $i\in I$. Subtraction would give $p^2+p+1=0\pmod{r_j}$, and then $p+2=0\pmod{r_j}$. Substitution would give $3=0\pmod{r_j}$. Lift the simple root to a class modulo $r_j^2$. Fixing $p$ in this class forces $r_j^2\mid F_j(p)$ and preserves squarefreeness locally at $r_j$ for $S$ and all present exponents.

Combine those classes with $p\equiv1\pmod {12}$ by the Chinese remainder theorem. Their joint class is reduced. In it, require $p+1$ and all $F_i(p)$, $i\in I$, to be squarefree at the remaining primes $r\ge5$. At each such prime the allowed local fraction is positive by the class $-2\pmod r$. Outside finitely many primes the quadratic polynomials have at most two simple roots each modulo $r$, hence at most two roots each modulo $r^2$. The number of forbidden unit classes modulo $r^2$ is at most $1+2|I|$, including the one from $p+1$. Consequently the product of the allowed fractions is strictly positive. For any fixed finite cutoff these fractions multiply by the prime number theorem in arithmetic progressions.

## Passing to all prime squares

For completeness, fix one quadratic $F(x)=Ax^2+Bx+B$ from the list. Its discriminant $\Delta=-3(A-3)(A+1)$ is a fixed negative integer. Take a fixed cutoff $R$ above all prime divisors of $2AB\Delta$. For each $r>R$ there are at most two roots modulo $r^2$, both units.

* For $R<r\le X^{1/4}$, Brun–Titchmarsh gives $O(X/(r(r-1)\log X))$ primes in those classes per $r$. Their combined cost is $O(\pi(X)/R)$.
* For $X^{1/4}<r\le X^{2/3}$, count all integers in the classes. Summing $O(X/r^2+1)$ gives $O(X^{3/4}+X^{2/3})$.
* For $r>X^{2/3}$, write $F(p)=h r^2$. Then $1\le h\ll_F X^{2/3}$, and $u=2Ap+B$ satisfies $u^2-Dr^2=\Delta$ with $D=4Ah$. If $D$ is a square, factor the left side. The number of pairs is $O_\Delta(1)$ for each $h$. Otherwise sort the positive solutions in each pair of residue classes $u,r\bmod |\Delta|$ by $\alpha=u+r\sqrt D$. For two consecutive values the ratio has integer coefficients in $1,\sqrt D$: the numerators $u_2u_1-Dr_2r_1$ and $r_2u_1-u_2r_1$ are divisible by $\Delta$. The ratio has norm one. If it exceeds one, half of the sum of the ratio and its reciprocal is an integer at least two. Successive values are therefore separated by a factor of at least $2+\sqrt3$. Since $1<\alpha=u+\sqrt{u^2-\Delta}\ll_F X+1$, there are $O_F(\log X)$ possibilities per $h$, uniformly in $D$. Summing over $h$ gives $O_F(X^{2/3}\log X)=o(\pi(X))$.

For $p+1$ the first two estimates suffice, since $r\le\sqrt{X+1}$. Taking $X\to\infty$ first and then $R\to\infty$, a union bound over the fixed finite list makes the omitted tail tend to zero relative to $\pi(X)$. The finite local products therefore give a positive-density subset realizing the prescribed pattern.

Finally, the full set realizing a pattern has a natural prime density. For every nonempty subset of exponents, simultaneous membership has a density by the same product-and-tail argument with no forced absences. The empty intersection has density $1/4$ among all primes when restricted to $p\equiv1\pmod{12}$. Finite inclusion-exclusion now gives the density for an arbitrary pattern. The positive-density subset constructed above makes this density positive.

## A second proof of the quadratic tail

Helfgott’s main theorem gives the prime-density Euler product for every cubic integer polynomial with no repeated root, including reducible cubics. Apply it to $G_i(x)=xF_i(x)$. This polynomial has no repeated roots because $F_i(0)\ne0$ and the quadratic has nonzero discriminant. On unit classes modulo $r^2$, the roots of $G_i$ are exactly those of $F_i$. For a prime input $p$ outside the finite set dividing $F_i(0)$, $p$ is coprime to $F_i(p)$, so $G_i(p)$ is squarefree exactly when $F_i(p)$ is.

The primes passing the square-divisor tests for $F_i$ through a fixed cutoff have density given by its finite Euler product. Subtracting Helfgott’s full limiting density gives the density of primes still failing at a larger prime. This difference tends to zero with the cutoff. The union over any fixed finite list of $i$ also has vanishing upper density. Restricting to the desired congruence class can only reduce this absolute error. [Helfgott, *Square-free values of f(p), f cubic*, Acta Mathematica 213 (2014), 107–135, main theorem](https://arxiv.org/pdf/1112.3820)

## Spacing between repeated square divisors

If a prime square $q^2$ with $q\ge5$ divides both $F_i(p)$ and $F_{i+t}(p)$, then $q^2\mid 2^t-1$. Indeed, putting $F(a,x)=a(x^2+x+1)-(x+2)^2$, direct expansion gives

$
((x+3)-bx)F(a,x)-((x+3)-ax)F(b,x)=3(a-b).
$

Substitute the two powers of two and cancel the factors coprime to $q$. For $1\le t\le19$, none of $2^t-1$ has a prime square factor of this kind. Gap 20 is attained at $p=37,q=5,i=6$. Lean 4.37.0-rc1 checked this identity, the finite bound and the example. [Lean certificate](DoublingObstructions.lean)

## Forcing arbitrarily many smaller-prime witnesses

For any prescribed pattern and any fixed $K\ge1$, a positive-density subset of the constructed primes $p$ has at least $K$ distinct smaller primes $q$ with $q+1\mid p+1$. Such a $p$ lies outside A082539.

Start with a bound $B$ larger than 3, the forced primes already used, and the number of present exponents plus two. Choose a prime $q\equiv1\pmod {4\prod_{3\le s\le B,\ s\text{ prime}}s}$ with $q+1$ squarefree. These primes have positive density for each fixed $B$: in the indicated residue class the tests at primes up to $B$ pass, each larger prime square removes one unit class, and the linear tail estimate above applies. Every prime divisor $s$ of $(q+1)/2$ exceeds $B$. Prescribe $p\equiv-1\pmod s$ at each such $s$. Of the $s$ lifts modulo $s^2$, one violates squarefreeness of $p+1$. Each present $F_i$ excludes at most one further lift: if $s\mid F_i(-1)=2^{i+1}-1$, then $F_i'(-1)=-2^{i+1}-2\equiv-3\pmod s$. A permitted lift therefore exists. The odd factors of $q+1$ are distinct, and $p$ is odd, so $q+1\mid p+1$. Repeat with $B$ increased past the preceding $q+1$. All new prime moduli are disjoint. Imposing these finitely many congruences preserves the positive product and the tail estimate. Removing primes $p$ below the largest $q$ has no effect on density.

## Explicit three-position witnesses

The bits below give membership at $4p^2,8p^2,16p^2$, in that order. All eight examples also satisfy squarefreeness of $3(p+1)$. For instance, for $p=688729$ the three nonsquarefree-divisor sums are divisible by $7^2,5^2,13^2$ respectively. The checker enumerates the divisors of each term directly and tests both sums by trial division. [Python checker](check_a300984_patterns.py)

| Pattern | Prime | Pattern | Prime |
|---|---:|---|---:|
| 000 | 688729 | 100 | 2029 |
| 001 | 157 | 101 | 229 |
| 010 | 7321 | 110 | 1237 |
| 011 | 109 | 111 | 13 |

## Sources and attribution

Michel Lagneau introduced the sequence in 2018. Codex developed the pattern argument for @dwilfand-sys. The quadratic tail extends the three fixed-exponent calculation already present in the A300984 density audit. The proof uses the classical prime number theorem in progressions, the Brun–Titchmarsh inequality, simple-root lifting and the Chinese remainder theorem. This is a mathematical proof on paper. The spacing lemma has a standalone Lean certificate. The density argument is a written proof, and historical priority remains unconfirmed.

[OEIS A300984](https://oeis.org/A300984) · [Prior density audit](https://github.com/dwilfand-sys/open-math-agents/tree/eb21c45aa89c8f3454c93a813ed25cf1e88a2bc1/research/A300984/audit) · [Brun–Titchmarsh notes](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/BrunTitchmarsh.pdf)

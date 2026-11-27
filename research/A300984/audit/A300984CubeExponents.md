# Square and cube exponents in A300984

Let $p$ be an odd prime, $i,j\ge2$, $A_i=2^{i+1}-1$, and $B_i=A_i-3$. The squarefree divisors of $2^ip^j$ have sum $S(p)=3(p+1)$. The other divisors have sum $T_{i,j}(p)=A_i(1+p+\cdots+p^j)-3(p+1)$. The established prime-shape theorem requires $p\equiv1\pmod {12}$ for membership.

## The cube column

For every fixed $i\ge2$ there is a term $2^ip^3$ in the sequence if and only if $i\not\equiv3\pmod6$. In each allowed exponent class a positive proportion of primes $p\equiv1\pmod {12}$ give both $2^ip^2$ and $2^ip^3$ simultaneously. For every allowed exponent, each of the four choices of membership for those two integers has positive natural prime density.

For the cube exponent,

$$
T_{i,3}(p)=(p+1)H_i(p),\qquad H_i(p)=A_i p^2+B_i.
$$

The square-exponent polynomial is $F_i(p)=A_i p^2+B_i p+B_i$. At 2, $p+1$ has valuation one, $H_i(p)$ is odd, and $F_i(p)$ is odd. At 3, the square-exponent condition always passes. If $3\nmid A_i$, then $H_i(p)\equiv 2A_i\not\equiv0\pmod3$. When $3\mid A_i$, $p^2\equiv1\pmod3$ gives $H_i(p)\equiv 2A_i-3\pmod9$. This vanishes precisely when $A_i\equiv6\pmod9$, equivalently $i\equiv3\pmod6$. In that case no admissible prime can give a cube-exponent term.

For an allowed $i$, every prime $r\ge7$ has at least six unit residues, of which at most five are $-1$ or roots of $F_i,H_i$. Neither quadratic vanishes identically modulo such $r$, because $\gcd(A_i,B_i)$ divides 3. A remaining residue avoids divisibility by $r$ in $p+1$, $F_i(p)$, and $H_i(p)$. At $r=5$, take $p\equiv-2$: then $F_i(-2)=3\cdot2^{i+1}$ and $H_i(-2)=5A_i-3$. These facts give local positivity at all primes.

For simultaneous squarefreeness apply the finite-product and tail argument from the finite-pattern theorem to the linear factor $p+1$ and both quadratics. They have no repeated roots. The extra requirement $\gcd(p+1,H_i(p))=1$ involves only primes dividing $H_i(-1)=2A_i-3$, a fixed nonzero integer. This proves positive natural density for simultaneous membership.

To force one or both absences independently, prescribe the square of a new prime as a divisor of the corresponding quadratic. For $F_i$ and $H_i$, choose distinct primes away from the constants, leading coefficients, discriminants, and values at $-1$. The two polynomials have no common root at any of these primes, because $F_i(x)-H_i(x)=B_i x$. The elementary prime-divisor construction and simple-root lifting in the finite-pattern proof give all the required congruences. The same local product and finite inclusion-exclusion prove positive density for each pattern.

## Exact local restrictions for an arbitrary exponent

For $p\equiv1\pmod {12}$ the following two tests depend only on $i,j$:

$$
4\mid T_{i,j}(p)\quad\Longleftrightarrow\quad j\equiv1\pmod4,
\qquad
9\mid T_{i,j}(p)\quad\Longleftrightarrow\quad A_i(j+1)\equiv6\pmod9.
$$

Modulo 4 the sum of the powers of $p$ is $j+1$, while $A_i\equiv3$ and $S(p)\equiv2$. Modulo 9 write $p=1+3u$. Binomial expansion gives $\sum_{k=0}^{j}p^k\equiv j+1+3u j(j+1)/2\pmod9$. If $3\nmid A_i(j+1)$, then $T_{i,j}$ is nonzero modulo 3. Otherwise $3\mid A_i j(j+1)/2$, so the term involving $u$ disappears modulo 9; $S(p)\equiv6\pmod9$. The excluded $j$ from the second test are $j\equiv5\pmod9$ for even $i$, $j\equiv1\pmod3$ for $i\equiv1\pmod6$, and $j\equiv0\pmod3$ for $i\equiv3\pmod6$. There is no exclusion from this test for $i\equiv5\pmod6$.

## Sources and status

Codex developed these exponent results for @dwilfand-sys from Michel Lagneau's sequence and the finite-pattern argument. These proofs concern additional structure of the sequence. The majority conjecture remains open, and neither Lean verification nor historical priority has been established for the assertions here.

[OEIS A300984](https://oeis.org/A300984) · [Finite-pattern theorem and analytic references](A300984FinitePatterns.md)

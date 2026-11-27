# A finite criterion for infinitely many exceptions in a divisibility class

Let $P(i,j)=(ij+i+j-\gcd(i,j))/2$ for $i,j\ge2$. A strongly nontriangular number is an integer $n>1$ outside the range of $P$, as in [OEIS A400795](https://oeis.org/A400795).

**Theorem.** Fix an even integer $K\ge2$. There are infinitely many strongly nontriangular numbers $n$ for which $K\mid n+1$ if and only if

$$
\text{for every divisor }d\ge3\text{ of }2K,\quad
\text{some prime divisor of }d-1\text{ does not divide }2K.
\tag{1}
$$

If (1) fails, every such $n\ge3K-1$ is represented. If (1) holds, then for all sufficiently large $T$ the number of such exceptions $n\le T$ is $\gg_K T/((\log T)^{3/2}\log\log T)$. They may be required to be squarefree and to have $n+1=Kp$, $p$ prime. For any fixed power of two one may prescribe any odd residue class of $p$ modulo that power without changing the order of this lower bound. Its implicit constant can then also depend on that modulus.

**Corollary.** Every odd residue class modulo every power of two contains infinitely many strongly nontriangular numbers, with the same order of lower bound and a constant depending on the modulus.

## Necessity

Suppose $d\mid2K$, $d\ge3$, and all prime factors of $d-1$ divide $2K$. For any $K\mid n+1$ we have $2n+1\equiv-1\bmod 2K$. If $n\ge3K-1$, then $e=2(n+1)/d\ge3$. Since $de=2(n+1)$, we have $e-1\equiv2n+1\bmod(d-1)$. Consequently $\gcd(d-1,e-1)=1$. The legs $d-1,e-1$ are both at least 2 and

$$
2P(d-1,e-1)=de-2=2n.
$$

This gives an explicit representation for every such $n$.

## Sufficiency

Assume (1). For each qualifying divisor $d$ choose one prime $\ell_d\mid d-1$ with $\ell_d\nmid2K$. Write $L$ for the product of the distinct chosen primes. Then $L$ is odd and $\gcd(L,2K)=1$. Because $K$ is even, $4\mid2K$, so $d=4$ forces $3\mid L$ and $3\nmid K$. Consider primes $X<p\le2X$ satisfying

$$
2Kp\equiv1\bmod L,\qquad n=Kp-1,\qquad N=2n+3=2Kp+1.
\tag{2}
$$

If desired, impose an arbitrary odd unit class for $p$ modulo a fixed power of two. One may also require $p\equiv1$ at each odd prime factor of $K$. Together these requirements define a reduced class modulo a fixed modulus $Q$ whose prime divisors include those of $2KL$.

In a representation with relatively prime legs, $(i+1)(j+1)=2Kp$. For $p>2K$, exactly one factor contains $p$, and the other is some $d\mid2K$, $d\ge3$. Its chosen prime $\ell_d$ divides $d-1$ and $2Kp-1=2n+1$, so it also divides the other leg. This contradicts relative primality. In a representation with gcd 2, set $i=2u$, $j=2v$ with $\gcd(u,v)=1$. As $n$ is odd, $u,v$ are both odd and $N=(2u+1)(2v+1)$ has a divisor 3 modulo 4. It suffices to arrange that all prime divisors of $N$ are 1 modulo 4. If all prime divisors of $n$ exceed $y=(\log X)^4$, every other possible gcd exceeds $y$ because $g\mid2n$ and $n$ is odd.

We verify that the sieve estimates from [the infinitude argument](Infinitude.md) transfer to (2). This verification is needed because its original coefficient is fixed there as $K=2$.

* For each odd prime $t\mid K$, the two forms take the values $n\equiv-1$ and $N\equiv1\bmod t$. For each $t\mid L$ they take $n\equiv-1/2$ and $N\equiv2\bmod t$. Thus the primes of $Q$ cause no sieving obstruction. At 2 both forms are odd.
* For the other primes $5\le t\le y$, the condition $t\nmid n$ forbids $p\equiv K^{-1}\bmod t$. If $t\equiv3\bmod4$, also forbid $p\equiv-(2K)^{-1}\bmod t$ for $t\nmid N$. These two reduced classes are distinct because $t\ne3$, and $3$ already divides $L$. For the primes $y<t<z=X^{1/(2+\eta)}$ in the inert class the sole forbidden class remains $-(2K)^{-1}$. Thus all local densities outside the fixed set are unchanged.
* The exact Bonferroni argument at $y$, followed by weighted Bombieri–Vinogradov and the half-dimensional sieve at level $D=X^{1/2-\eta/16}$, applies on the fixed progression modulo $Q$. Each modulus is $Qde$ and the factor $Q$ is coprime to $de$. Removing the primes of $Q$ changes the product constants by fixed factors only. The pre-switch lower bound is at least $c_Q\sqrt{\eta}\,X/((\log X)^{3/2}\log y)$ for a fixed positive $c_Q$ independent of small fixed $\eta$ and sufficiently large $X$ depending on $Q,\eta$.
* Because $N\equiv1\bmod4$, an exception remaining after the lower sieve has exactly two prime factors 3 modulo 4, counted with multiplicity. Write $N=kqr$ as in the original proof. For $H=kq$ one has $p=(Hr-1)/(2K)$ and $n=(Hr-3)/2$. Let $Y=(4KX+1)/H$, $b=Y^{1/400}$. At each $5\le t\le b$ with $t\nmid2KQH$, the same switched forbidden classes for $r$ are $0,H^{-1}$, and additionally $3H^{-1}$ when $t\le y$. At $t\mid H$, $t\nmid2KQ$, only 0 is required. Omit the finitely many primes of $2KQ$ on the upper bound. The integer Selberg sieve with these roots has the same two logarithmic factors and further factor $1/\log y$, with a constant depending on the fixed excluded prime set.
* The split-factor variable is bounded by $B=(4KX+1)/z^2$, and $q\le\sqrt{4KX+1}$. The harmonic estimates in Section 4 of the original argument give $O_K(\sqrt{\eta\log X})$ and $O_K(\eta)$, respectively, as $X$ grows for fixed $\eta$. Thus the switched loss is at most $C_{K,Q}\eta^{3/2}X/((\log X)^{3/2}\log y)$ plus a power-saving error. Choosing $\eta$ sufficiently small in terms of $K,Q$ leaves a positive constant times $X/((\log X)^{3/2}\log y)$.

The number of integers $n\le2KX$ having any representation with $g>y$ is $O_K(X\log X/y)$ by $g^2uv\le2n$ for reduced legs $u,v$. The number of survivors divisible by the square of a prime is $O_K(X/y)$, because every prime factor exceeds $y$. Both errors are smaller than the surviving lower bound. Taking $X=T/(2K)$ proves sufficiency.

For the corollary set $K=2^h$, $h\ge1$. Every $d\ge3$ dividing $2K$ is a power of two at least 4, so $d-1$ has an odd prime factor and (1) holds. Let $a\bmod2^b$ be odd. If $a\not\equiv-1\bmod2^b$, take $h=v_2(a+1)$ and prescribe $p\equiv(a+1)/2^h\bmod2^{b-h}$. If $a\equiv-1\bmod2^b$, any $h\ge\max(1,b)$ works. In both cases $n=2^hp-1$ belongs to the requested class.

The criterion and specialization are Codex research for @dwilfand-sys based on the classical sieve inputs cited in the infinitude argument. The argument is written on paper. Historical priority and kernel verification are unconfirmed.

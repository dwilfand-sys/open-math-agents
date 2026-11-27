# OEIS A085265. A positive square and a squarefree remainder

For each positive integer other than 1 and 13, the argument gives a positive square and a positive squarefree remainder. The finite ranges have reproducible integer certificates in **squarefree_moderate.py**. The general argument below is mathematical working material. Formalization of the nonsquarefree-input case in Lean is in progress.

Let $n\geq 2$, $U=\lfloor\sqrt{n-1}\rfloor$, and choose $e=1$ if
$4\mid n$ and $e=0$ otherwise. Put $J=\lfloor(U+e)/2\rfloor$.
The admissible square roots are $k_j=2j-e$, $1\leq j\leq J$.
They satisfy $1\leq k_j\leq U$, $4\nmid n-k_j^2$, and $U\leq 2J+1$.

Let $B$ be the product of the distinct odd primes $p$ such that $p^2\mid n$. Their squares are pairwise coprime and divide $n$, so $B^2\mid n$ and $B\le U+1\le 2J+2$.
Write $r=\omega(B)$, $\rho=\prod_{p\mid B}(1-1/p)$, and $G$ for the number
of admissible $j$ with $n-k_j^2$ squarefree. Define $E_0=0$ when $r=0$
and $E_0=2^{r-1}$ when $r>0$. Let $\pi_o(X)$ count odd primes up to and
including $X$.

## An explicit bound

For any integer $1\leq T\leq U$, write $R=\sum_{p\text{ odd prime}}1/p^2$.
Then

$$
G\ \geq\
J\left[\rho\left(1-2R+2\sum_{p\mid B}\frac1{p^2}\right)
             -\frac{1-\rho}{T}\right]
-E_0-\pi_o(U)-(2^r-1)\pi_o(T).
$$

One may replace $1-2R$ by $29/50$. Indeed, listing the odd primes below
39 and bounding the rest by all odd integers from 39 onward gives
$$
R<\sum_{p\in\{3,5,7,11,13,17,19,23,29,31,37\}}\frac1{p^2}
     +\frac1{76}<\frac{21}{100}.
$$
The last inequality is rational arithmetic. The first follows by telescoping
$1/(m^2-1)=(1/(m-1)-1/(m+1))/2$ over odd $m\geq39$.
The same identity gives $\sum_{p>T,\ p\ {\rm odd}}1/p^2\leq 1/(2T)$
for integral $T\geq1$.

## Counting the candidate roots

We first retain $j$ for which $\gcd(k_j,B)=1$. For each $d\mid B$,
the number $N_d$ of indices with $d\mid k_j$ has main term $J/d$.
For $e=0$ it equals $\lfloor J/d\rfloor$. In
$\sum_{d\mid B}\mu(d)N_d$, the error terms with $\mu(d)=-1$ have
nonnegative sign. Only the $2^{r-1}-1$ nonempty, even-cardinality subsets
can reduce the total when $r>0$. For $e=1$,
$$
N_d=\left\lfloor\frac{J+(d-1)/2}{d}\right\rfloor .
$$
As $d$ is odd, its distance from $J/d$ is strictly less than $1/2$.
The empty subset is exact, and the other $2^r-1$ subsets contribute total
absolute error strictly below $(2^r-1)/2$. Both parities therefore leave at
least $\rho J-E_0$ indices, including the case $B=1$.

For retained $j$, a prime dividing $n$ cannot have $p^2\mid n-k_j^2$.
If this divisibility held, $p\mid k_j$ and hence $p^2\mid n$, so $p\mid B$
for odd $p$. The choice of parity already excludes $p=2$. Every bad
retained index must therefore be removed by an odd prime $q\leq U$ with
$q\nmid n$ for which $x^2\equiv n\bmod q^2$ is soluble. Call these
primes active. At an active prime the roots are a distinct opposite pair.
Indeed, for any two roots $x,y$, $q^2\mid(x-y)(x+y)$ and $q$ cannot
divide both factors since $q\nmid 2x$.

## The paired residue count

Fix an active $q$ and $d\mid B$. Modulo $m=dq^2$, the conditions
$d\mid k_j$ and $q^2\mid n-k_j^2$ select two classes. The Chinese
remainder theorem gives one class of $k_j$ for each root modulo $q^2$
and those two classes are negatives of each other. Multiplication by 2 is
invertible modulo $m$. Thus the two classes of $j$ are exchanged by
$j\mapsto e-j\bmod m$.

Take the representatives in $1,\ldots,m$. For $e=0$, their sum is $m$
since neither is 0 modulo $q$. For $e=1$, their sum is $m+1$, also when
one representative is $m$. As $m$ is odd and the two classes are distinct,
one representative belongs to $1,\ldots,\lfloor m/2\rfloor$ and the other
belongs to $\lfloor m/2\rfloor+1,\ldots,m$. A prefix of length
$0<t<m/2$ contains zero or one representative. A prefix with
$m/2<t<m$ contains one or two. In both intervals the count differs from
$2t/m$ by strictly less than 1. At the empty prefix the error is zero.
Complete blocks contribute exactly two each, so the simultaneous congruences
have $2J/(dq^2)+\varepsilon_{d,q}$ solutions with
$\lvert\varepsilon_{d,q}\rvert<1$.

Inclusion–exclusion over $d\mid B$ bounds the number of retained indices
hit by $q$ above by $2\rho J/q^2+2^r$. Taking $d=1$ without imposing
coprimality also gives the integer bound $1+\lfloor 2J/q^2\rfloor$.
In particular there is at most one hit if $q^2>2J$.

## Summing the bounds

Use the coprimality bound for active $q\leq T$ and the unrestricted bound
for larger active $q$. The total constant term in this union bound is at most
$\pi_o(U)+(2^r-1)\pi_o(T)$. The terms proportional to $J$ are bounded by
$$
2\rho J\sum_{q\ {\rm active}}\frac1{q^2}
 +2(1-\rho)J\sum_{q>T,\ q\ {\rm active}}\frac1{q^2}.
$$
The first reciprocal sum is at most $R-\sum_{p\mid B}p^{-2}$ because active
primes are disjoint from $B$. Applying the telescoping tail bound to the second
sum gives the stated inequality. All union and inclusion–exclusion steps use
finite sets. The infinite reciprocal sums can equivalently be replaced by the
finite sum up to $\max(U,B)$ and the same rational upper bounds.

## The finite range

For $J<300$, the preceding inequalities give $n\le(2J+2)^2\le360000$. A sieve marks as nonsquarefree every positive multiple of $d^2$ for $d\ge2$ up through $\lfloor\sqrt{365000}\rfloor$. For each positive $n\le365000$ the program tests the square roots starting at 1 and ending at $\lfloor\sqrt{n-1}\rfloor$. The only missing inputs are 1 and 13. Every other input in this range has a witness with root at most 14.

## The intermediate range

Let $C(h)=\sum_{3\le p\le 2h+1}(1+\lfloor 2h/p^2\rfloor)$, with the sum over odd primes. If $L\le J\le H$, the first counting argument gives

$$
G\ge L\rho-E_0-\sum_{\substack{3\le p\le2H+1\\p\notin S}}
        (1+\lfloor2H/p^2\rfloor),
$$

where $S$ is the set of divisors of $B$ lying in $\{3,5,7,11,13,17\}$. Each of those primes can be excluded because the candidate roots are coprime to $B$. For a fixed $S$, suppose $B$ has $t$ additional prime factors. Replacing them, in order, with the first $t$ primes from 19 onward can only decrease their product and the product of the factors $1-1/p$. Thus this replacement both enlarges the set of eligible profiles $B\le2H+2$ and gives a lower bound for $\rho$. The bound $E_0$ depends only on $r=|S|+t$.

The implementation `squarefree_moderate.py` begins with $L=300$, uses $H=\min(10^6,L+\lfloor L/60\rfloor)$, and starts the following interval at $H+1$. It checks the displayed strict inequality after clearing denominators for all profiles. This takes 485 intervals and 59,373 integer comparisons. The prime table includes every candidate prime through $2\cdot10^6+1$.

## The unbounded range

Assume $J\ge10^6$, let $r=\omega(B)$, and write $F=\rho(29/50+2\sum_{p\mid B}p^{-2})$. The counting inequality implies the weaker estimate

$$
G\ge FJ - J/T - \pi(2J+2) - (1+2\pi(T))2^r.
$$

Here $\pi(x)$ counts all primes. A smaller error $ (1+2\pi_o(T))2^r$ also works, with $\pi_o$ counting odd primes. When $T=128$, the bound $63\cdot2^r$ follows from $\pi_o(128)=30$. For a cutoff $H=2^s$, the elementary bound on the primorial yields

$$
\pi(2J+2)\le \pi(H)+(4J+4)/s.
$$

Indeed, every prime greater than $H$ contributes at least $2^s$ to their product and the full primorial is at most $4^{2J+2}$.

For $r\le9$, a lower bound for $F$ is obtained by splitting according to $3\mid B$. When $3\mid B$, retain $2/9$ in the sum and bound $\rho$ below by the product of the first $r$ odd-prime factors $1-1/p$. When $3\nmid B$, take the first $r$ primes from 5 onward. This gives the following rational bounds. The last column is the remaining positive margin at the smallest $J$, after allowing $J/128+63\cdot2^r$ and the specified prime-count bound. Its coefficient of $J$ is positive in every row.

| $r$ | Lower bound for $J$ | Lower bound for $F$ | $s$ | Upper bound for $\pi(2^s)$ | Margin |
|---|---:|---:|---:|---:|---:|
| $0$ through $6$ | 1,000,000 | $36/125$ | 16 | 22,000 | $16621/4$ |
| $7$ | 2,400,000 | $34/125$ | 16 | 22,000 | $15943/4$ |
| $8,9$ | 55,000,000 | $1/4$ | 18 | 262,144 | $14466421/18$ |

The stronger lower bounds for $J$ follow from $2J+2\ge B$ and the products $4,849,845$ and $111,546,435$ of the first seven and eight odd primes. The bound at $2^{16}$ also follows by counting the two residues $\pm1\bmod 6$ and the two exceptional primes 2 and 3.

At $r=10$, the first ten odd primes give $\rho>3/10$. The $i$-th odd prime is at least $i$, so multiplying by later factors gives $\rho\ge3/r$ by telescoping. The product of the first ten odd primes is 100,280,245,065. This gives $J\ge4r8^r$ at $r=10$, with room to spare. Each subsequent odd prime is greater than 11, whereas $4(r+1)8^{r+1}/(4r8^r)\le8.8$, which preserves the bound (including the two-unit slack in $B\le2J+2$).

Take $T=16r$ and $H=8^r$. The primorial bound yields $\pi(2J+2)\le H+(4J+4)/(3r)\le(8/5)J/r$. There are at most $8r$ odd primes up to $16r$. Therefore the remaining constant loss is at most $(16r+1)2^r\le J/(100r)$, using $100(16r+1)\le4\cdot4^r$ for $r\ge10$. The tail costs at most $J/(16r)$. The main term is at least $87J/(50r)$, which strictly exceeds $ (8/5+1/16+1/100)J/r$.

## Relation to the published result

Theorem 1 of J. Jiménez Urroz, *Every integer can be written as a square plus a squarefree*, Expositiones Mathematicae 40 (2022), 665–678, allows a zero square. It supplies the first hypothesis in the reduction as stated in the paper. The independent argument here handles the prime squares dividing $n$ explicitly. In the 2020 arXiv version the first inequality of Section 5 sums over primes not dividing $n$ after subtracting a primitive representation count from $\lfloor\sqrt n\rfloor$. At $n=4$ its left side is 1 and its right side is 0. The sources checked here do not resolve whether the corresponding expression changed in final typesetting.

[Published article](https://doi.org/10.1016/j.exmath.2021.12.002) · [Preprint](https://arxiv.org/abs/2010.15580) · [OEIS A085265](https://oeis.org/A085265)

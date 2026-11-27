# A second proof that the insertion sequences can have irrational digit frequency

John W. Layman's conjecture C.1 asks whether every ratio-determined insertion sequence satisfies a recurrence of type $(C,D)$ for positive integers $C,D$. The original parameter range is all real $0<k\le1$. The argument below gives uncountably many distinct counterexamples by varying a continuously defined rotation number. It also excludes the proposed recurrence after any finite starting segment. The argument applies to the real-parameter conjecture; it gives no rational counterexample.

## The ratio update

Fix an integer $m\ge2$. Write $1/k=m+1-c$, where $0\le c\le1$, and define $a_0=0,a_1=1$. The insertion successor formula gives

$$
d_n=1+\left\lfloor 1/k+a_{n-1}/a_n\right\rfloor,
\qquad a_{n+1}=d_n a_n-a_{n-1}.
$$

To recall this formula, at the first stable gap after the leftmost 1 its right endpoint is the least integer strictly greater than $1/k$. At the birth of each later stable right endpoint $a_n$ its neighbor on the right is $a_n-a_{n-1}$: the gap on its left was obtained by splitting the preceding gap at the sum of its endpoints. Repeated splits starting from that new gap on the right keep the left endpoint $a_n$ and increase the right endpoint by $a_n$ each time. The first stable right endpoint is the first candidate $j a_n-a_{n-1}$ strictly greater than $a_n/k$. Splits farther right never alter these neighbors; once a gap is stable its endpoints stay adjacent. This establishes the formula inductively for every finite prefix, including equality in the insertion test. The general floor formula and a prior proof are given in [NiuVector's proof note for A085260](https://github.com/NiuVector/A085260-proof/blob/main/proof_note_en.md). [Layman's original conjecture](https://personal.math.vt.edu/layman/sequences/ins_seq.htm)

Writing $r_n=a_{n-1}/a_n$, we have $r_1=0$ and $r_{n+1}=1/(d_n-r_n)$. Each $r_n$ belongs to $[0,1)$ and $a_{n+1}>2a_n$ because $d_n\ge3$ and $r_n<1$. Call $d_n=m+2$ a high digit. The low digit $m+1$ occurs at $r_n<c$ and the high digit at $r_n\ge c$.

## Replacing a jump by a flat interval

Define a lift $F_c$ on the real line by $F_c(x+1)=F_c(x)+1$ and, on $0\le x<1$, by

$$
F_c(x)=
\begin{cases}
1/(m+1-x),&x<c,\\
1+1/(m+2-x),&x\ge c.
\end{cases}
$$

Starting at zero, the fractional parts of its iterates are $r_{n+1}$, and $\lfloor F_c^n(0)\rfloor$ is the number of high digits in the first $n$ steps. The lift is increasing, with one jump per unit interval for interior parameters. Move its jump to the integer boundary by putting $H_c(x)=F_c(x+c)-c$. On $0\le x<1$ **both** formulas simplify to

$$
H_c(x)=1-c+\frac1{m+2-c-x}.
$$

Put $A_c=1-c+1/(m+2-c)$ and $B_c=1-c+1/(m+1-c)$. We have $A_c<B_c<A_c+1$ for all $c\in[0,1]$. Define $K_c$ first on $[A_c,A_c+1]$ by

$$
K_c(y)=
\begin{cases}
m+2-c-1/(y-1+c),& A_c\le y\le B_c,\\
1,& B_c\le y\le A_c+1,
\end{cases}
\qquad K_c(y+1)=K_c(y)+1.
$$

The two formulas agree at $B_c$. The values at $A_c,A_c+1$ are 0 and 1, so the degree-one extension is continuous. The map is nondecreasing and $K_c(H_c(x))=x$ for every real $x$, including integer endpoints. Also $(c,y)\mapsto K_c(y)$ is continuous. The boundaries $A_c+j,B_c+j$ are continuous functions of $c$ for integers $j$, the inverse formula on its closed domain has a positive denominator, and the neighboring formulas agree on their shared boundaries. On each compact set only finitely many pieces occur. Compactness on $[0,1]^2$ gives continuity in $c$ in the uniform norm on one period.

## Continuity of the rotation frequency

For completeness, let $K$ be a continuous nondecreasing degree-one lift. Set $u_n=\min_x(K^n(x)-x)$ and $v_n=\max_x(K^n(x)-x)$ on one period. Monotonicity and periodicity imply $v_n-u_n\le1$: when $x\le y\le x+1$, one has $K^n(x)\le K^n(y)\le K^n(x)+1$. The sequence $u_n$ is superadditive and $v_n$ is subadditive. Hence $u_n/n$ and $v_n/n$ have the same limit $\rho(K)$, with $u_n\le n\rho(K)\le v_n$ for every $n$. In particular

$$
|K^n(x)-x-n\rho(K)|\le1
$$

uniformly in $x$. For the family $K_c$ its finite iterates depend continuously on $c$. The displayed bound shows that $\rho(K_c)$ is continuous, being the uniform limit of the continuous functions $K_c^n(0)/n$.

Taking $x=H_c^n(y)$ in this bound gives $|H_c^n(y)-y+n\rho(K_c)|\le1$. Translation conjugacy gives the same estimate for $F_c^n(y)-y$. Consequently the limiting frequency of high digits, starting from the original $r_1=0$, exists and equals $-\rho(K_c)$. At $c=0$ every digit is high, while at $c=1$ every digit is low. Continuity therefore realizes every frequency in $[0,1]$ for at least one $c\in[0,1]$.

## Why the proposed recurrence cannot hold

Suppose some tail satisfies $a_{n+2D}=C a_{n+D}-a_n$. For $C=1$ roots of the characteristic polynomial are nonreal of modulus one; for $C=2$ the double root 1 gives at most linear growth along each residue class. Both contradict $a_{n+1}>2a_n$. For $C\ge3$ the roots are $\lambda>1$ and $\lambda^{-1}$. Every residue class therefore has the form $a_{j+D\ell}=u_j\lambda^\ell+v_j\lambda^{-\ell}$ for sufficiently large $\ell$, with $u_j>0$ by positivity and growth. Ratios $a_{n+1}/a_n$ and $a_{n-1}/a_n$ each converge along every residue class modulo $D$, including at the wrap from one block to the next. Their sum is the integer digit $d_n$, so it is eventually constant along each class. Such a digit sequence has rational limiting high-digit frequency. Choosing any irrational frequency in the previous construction contradicts the recurrence. Distinct frequencies give distinct sequences.

## Exact classification, including every rational insertion parameter

The same lift applies for $m=1$: the denominator $m+1-c$ is at least 1, and $B_c-A_c=1/[(m+1-c)(m+2-c)]\le1/2$. For all $m\ge1$, the ratio $a_{n+1}/a_n=d_n-r_n$ is strictly greater than 1, and on a high digit it is strictly greater than 2. Write $\alpha$ for the limiting high-digit frequency, already proved to exist. We now prove that the sequence obeys Layman's recurrence for all its terms if and only if $\alpha$ is rational. In particular, every rational $k\in(0,1]$ obeys it.

**The orbit of zero determines a mechanical digit word.** Set $h_n=\lfloor F_c^n(0)\rfloor$ for $n\ge0$. Monotonicity and degree one give
$$
h_n+h_m\le h_{n+m}\le h_n+h_m+1.
$$
Indeed $h_n\le F_c^n(0)<h_n+1$, and $F_c^m$ applied to the two bounding integers gives two numbers exactly one unit apart, with respective floors $h_n+h_m$ and $h_n+h_m+1$. Fixing $n$, iterating this inequality at multiples of $n$ and dividing by the number of multiples gives
$$
h_n\le n\alpha\le h_n+1 .
$$
Consequently $h_n=\lfloor n\alpha\rfloor$ whenever $n\alpha$ is not an integer. If $\alpha=a/b$ in lowest terms ($b=1$ at either endpoint), all exceptional indices are multiples of $b$. Consider the nondecreasing lift $G(x)=F_c^b(x)-a$. If $G(0)\ge0$, every $G^j(0)\ge0$; if $G(0)<0$, then $G^j(0)\le G(0)<0$ for every $j\ge1$. As $G^j(0)=F_c^{bj}(0)-ja$, this means either $h_{bj}=ja$ for all $j\ge1$ or $h_{bj}=ja-1$ for all $j\ge1$. Hence for $n\ge1$ the sequence $h_n$ is either $\lfloor n\alpha\rfloor$ at every index or $\lceil n\alpha\rceil-1$ at every index. In both cases $h_{n+b}=h_n+a$ for $n\ge1$, so the digits $d_n=m+1+h_n-h_{n-1}$ are $b$-periodic for every $n\ge2$. The possibly exceptional first digit has been accounted for by $a_2$.

For $j\ge1$, start from the state $(a_{j+1},a_j)^T$ and apply one period of the matrices $M_d=\left(\begin{smallmatrix}d&-1\\1&0\end{smallmatrix}\right)$, beginning with $d_{j+1}$. Their period product $P_j$ has determinant one and the same integer trace $C$ for all $j$, since all the products are cyclic permutations of the same factors. In the coordinates $(u,u-v)$ each matrix acting on $(u,v)$ instead has the form $\left(\begin{smallmatrix}d-1&1\\d-2&1\end{smallmatrix}\right)$. For $d\ge2$ all entries are nonnegative and both diagonal entries are at least one. The same holds for their product, giving $C\ge2$ even for the all-low case $m=1$. The next block has the same product $P_j$. The identity $P_j^2-CP_j+I=0$ on the second state coordinate therefore gives
$$
a_{j+2b}=C a_{j+b}-a_j \qquad (j\ge1).
$$
Conversely, if $\alpha$ is irrational, it is strictly positive and the high steps $a_{n+1}/a_n>2$ already give exponential growth $a_{n+1}\ge 2^{h_n}$. The proof in the preceding section excluding any tail recurrence now applies also for $m=1$.

**A rational threshold has a finite inverse orbit.** For a rational $k$ choose $m=\lfloor1/k\rfloor\ge1$ and $c=m+1-1/k\in(0,1]$. If $0<c<1$, write $f$ for the ratio map on $[0,1)$, namely $f(x)=1/(m+1-x)$ for $x<c$ and $f(x)=1/(m+2-x)$ for $x\ge c$. For $0<y=u/v<1$ with $u,v$ coprime, every preimage has the form $m+1+e-v/u$ with $e\in\{0,1\}$. Its denominator in lowest terms divides $u<v$. Both branches are injective and their image ranges are disjoint: the high branch takes values strictly below $1/(m+1)$, the low branch takes values at or above it. In particular there is at most one preimage. Starting from the rational point $c$, its backward orbit must terminate, since denominators of interior points strictly decrease at each inverse step and 0 itself has no preimage. There is also no preimage of 1.

Partition $[0,1)$ at 0 and all points of that finite backward orbit, taking cuts as singleton atoms and the intervals between consecutive cuts (including the final interval to 1) as open atoms. A singleton has a unique image point and therefore determines a unique next atom. On each open atom $f$ is continuous and its image avoids every cut: a preimage of a cut would already be among the cuts. Hence each atom determines a unique next atom and a unique digit. Finite deterministic iteration yields an eventually periodic atom sequence starting at 0, including any exact visit to $c$, where the high digit is chosen. Its high-digit frequency $\alpha$ is rational. The preceding argument then proves the recurrence at **every** $j\ge1$, even before the finite atom orbit settles into a cycle.

For $c=1$, equivalently $1/k=m$, the digit is always $m+1$. At $m=1$ this gives $a_n=n$ and $C=2,D=1$. The alternative endpoint convention $c=0$ also has a constant digit, equal to $m+2$, and represents the same parameter as $m+1,c=1$. These endpoints satisfy the same conclusion directly. Thus on the common interpretation with rational insertion ratio Layman's C.1 holds without a transient, whereas the stated real parameter range admits the counterexamples above.

## A sharp bound for rational parameters

Let $k=p/q$ in lowest terms. The denominator $b$ of the digit frequency is at most $p$. For $0<c<1$ the denominator of $c=m+1-q/p$ is exactly $p$. Each interior point of its backward orbit has a distinct reduced denominator in $\{2,\ldots,p\}$. Hence there are at most $p-1$ interior cuts and at most $p$ open interval atoms. A forward orbit starting on a cut must eventually leave the cuts. Indeed 0 is never an image, every interior cut on the inverse chain maps forward along that chain to $c$, and $c$ cannot itself map into the chain: that would make it periodic and give an infinitely long inverse chain despite strict denominator descent. Once in an open atom the orbit stays in open atoms. Its eventual atom period is at most $p$, so the denominator of the limiting high-digit frequency is at most $p$. The endpoint $c=1$ has $b=1$.

This bound is attained for every numerator $p\ge2$ by $k=p/(p+1)$. Here $m=1$ and $c=(p-1)/p$. The initial low-digit progression $a_n=n$ first meets the high threshold at $n=p$ because $r_n=1-1/n$. Then $a_{p+1}=2p+1$, and each successive low step maintains the increment $p+1$. At $n=p+1+j$ the prospective ratio from those low steps is
$$
1-\frac{p+1}{2p+1+j(p+1)} .
$$
It first reaches $c$ when $j=p-1$: at $j=p-2$ the denominator is $p(p+1)-1$. Thus the next high digit occurs at step $2p$. It follows that $h_p=h_{2p-1}=1$, hence $1/p\le\alpha\le2/(2p-1)<1/(p-1)$. The only rational in this range with reduced denominator at most $p$ is $1/p$. Moreover, any recurrence step $D$ for this sequence must be divisible by $p$: positive high frequency ensures exponential growth, and the residue-class argument shows that the integer digits are eventually $D$-periodic. For $p=1$ the bound 1 is also attained.

These are written arguments. Historical priority and Lean verification have not been established.


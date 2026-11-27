# Every exceptional insertion parameter is transcendental

Every real **algebraic** insertion ratio $0<k\le1$ satisfies John W. Layman's proposed recurrence for some positive integers $C,D$, at every index $a_{j+2D}=Ca_{j+D}-a_j$ with $j\ge1$. The [rotation argument](InverseLift.md) constructs exceptional real ratios, and the theorem here shows that every one of them is transcendental. The proof uses Yann Bugeaud's published complexity theorem for regular continued fractions. This is a written mathematical argument; its application to the insertion problem has no Lean verdict or established historical priority. [Layman's ratio range and conjecture C.1](https://personal.math.vt.edu/layman/sequences/ins_seq.htm) · [Bugeaud, Theorem 1.1](https://doi.org/10.24033/asens.2208)

## The inverse digits of an exceptional threshold

Put $m=\lfloor1/k\rfloor\ge1$, $c=m+1-1/k$. The ratio map on $[0,1)$ uses $U_e(x)=1/(m+1+e-x)$, with $e=0$ if $x<c$ and $e=1$ if $x\ge c$. Suppose $k$ is exceptional. By the classification its high-digit frequency $\alpha$ is irrational, so $0<\alpha<1$ and $0<c<1$. The argument in [the size estimate](Dimension.md) proves two facts, which we briefly recall.

1. The full backward orbit of $c$ is an infinite chain. The two branch images are disjoint and there is at most one preimage per point. If the chain terminated, cuts at 0 and the finitely many preimages of $c$ would give each interval or singleton atom a unique successor atom and digit. The orbit of 0 would have a periodic tail, contradicting irrational frequency.
2. Along **every** forward segment of length $t$ the number of high digits is either $\lfloor t\alpha\rfloor$ or $\lceil t\alpha\rceil$. Indeed the integer displacement of a lift started at 0 is $\lfloor t\alpha\rfloor$, and starting anywhere in $[0,1)$ changes it by at most one by monotonicity and degree one. For a segment of length $n$ the partial sums $s_i$ of its digits therefore satisfy $s_i=\lfloor i\alpha+\beta\rfloor$, $0\le i\le n$, for some $0\le\beta<1$: the discrepancies $s_i-i\alpha$ have width less than one, so take $\beta$ to be their maximum, including $s_0=0$.

Write $x_0=c$ and let $x_{-j}$ be its unique $j$-step preimage. Define $e_j$ as the digit on the step **from** $x_{-j}$ **to** $x_{1-j}$, for $j\ge1$. The infinite word $e_1e_2\ldots$ thus reads the chain backwards. Each contiguous block is the reversal of a forward segment. Its high count differs from its length times $\alpha$ by less than one. In particular the word has irrational high frequency $\alpha$, is not ultimately periodic, and its gaps between highs are bounded by $H=\lceil1/\alpha\rceil$, since each block of length $H$ contains a high.

For a fixed $\alpha$, there are at most $n+1$ possible length-$n$ forward words. As $\beta$ ranges over $[0,1)$, the floors for $i=1,\dots,n$ change only at the $n$ points $\{-i\alpha\}$. At each boundary the floor function takes its value on the interval immediately to the right. Reversing all these words preserves their number. Hence the backward word has factor complexity $p_e(n)\le n+1$, where complexity counts distinct contiguous blocks of a given length in this one infinite word.

## Conversion to a regular continued fraction

Put $d_j=m+1+e_j$. Then $c=U_{e_1}\circ\cdots\circ U_{e_N}(x_{-N})$. Replacing $x_{-N}$ by 0 changes the result by at most $4^{-\lfloor N\alpha\rfloor}$, because the branch derivatives on $[0,1]$ are at most 1 for either digit and at most $1/4$ for a high digit. It follows that $c$ has the infinite negative continued fraction with digits $d_1,d_2,\ldots$, that is, its successive denominators use subtraction. The corresponding regular continued fraction, provisionally allowing zeros, is
$$
c=[0;d_1-1,1,d_2-2,1,d_3-2,1,\ldots].
$$
For a finite truncation at $N$ the same equality holds with the final pair $d_N-2,1$ (for $N=1$ the list is simply $d_1-1,1$). One way to check the identity, recursively from the last digit, is to write
$$
d-t=(d-1)+\frac1{1+t/(1-t)},\qquad
\frac{1/(d'-u)}{1-1/(d'-u)}=\frac1{d'-1-u}.
$$
Here the inner tails $t,u$ are in $[0,1)$, so every displayed division is valid.

When $m\ge2$, all regular partial quotients are positive. After a fixed prefix they alternate the constant 1 with $m-1+e_j$. A block of length $n$ is specified by the starting parity and a block of at most $\lceil n/2\rceil+1$ successive input digits. The regular word therefore has complexity $O(n)$. If it were ultimately periodic, reading its even or odd positions carrying $m-1+e_j$ would give eventual periodicity of $e_j$, which is impossible.

When $m=1$, the regular word after its first partial quotient has the provisional form $1,e_2,1,e_3,1,\ldots$. Remove zeros via the regular-CF identity $(A,0,B)\mapsto (A+B)$, as follows directly by composing $x\mapsto1/(a+x)$ for the three partial quotients. Let $j_1<j_2<\dots$ enumerate high indices among $j\ge2$, and $g_i=j_{i+1}-j_i$. Between two successive high partial quotients (each equal to 1) the substring of separating 1s and zeros collapses to the single positive partial quotient $g_i$. The resulting regular expansion thus has a finite prefix followed by the alternating string $1,g_1,1,g_2,1,g_3,\ldots$. To see convergence with boundary conventions, one can truncate the negative fractions at successively larger high indices. The finite zero eliminations stabilize each finite prefix of the resulting positive regular word. The ordinary positive continued-fraction convergents converge to the same limit, since their cylinder diameters tend to zero.

All $g_i$ are at most $H$. A block of $n$ gaps is specified by an input block of length $Hn+1$ starting at a high digit: the positions of its next $n$ highs determine the gaps. Thus $p_g(n)\le p_e(Hn+1)\le Hn+2$. Adding the intervening 1s and a fixed prefix preserves linear complexity. Ultimate periodicity of the regular expansion would make $g_i$ ultimately periodic by taking every other digit; a periodic list of gaps reconstructs an ultimately periodic binary word. This again contradicts irrational high frequency. The argument covers runs of consecutive highs, which give gap 1, as well as long runs of lows.

## Application of Bugeaud's theorem

Bugeaud's Theorem 1.1 applies to an infinite, not ultimately periodic sequence of **positive integer** regular partial quotients. It states that if the resulting number is algebraic, then its complexity divided by the block length tends to infinity. Our positive regular expansion in each case is not ultimately periodic and its complexity is $O(n)$. Therefore $c$ is transcendental. Since $k=1/(m+1-c)$ is related to $c$ by an invertible rational fractional-linear transformation, $k$ is also transcendental. By contraposition every algebraic insertion ratio has rational digit frequency and satisfies the exact recurrence from the rotation classification. The result is a necessary condition for an exception; many transcendental parameters also lie on constant-recurrence intervals. [Bugeaud, *Automatic continued fractions are transcendental or quadratic*, Ann. Sci. Éc. Norm. Supér. 46 (2013), 1005–1022, Theorem 1.1](https://doi.org/10.24033/asens.2208)

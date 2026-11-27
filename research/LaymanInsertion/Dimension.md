# Size of the exceptional set of insertion ratios

Let $\mathcal E$ be the set of real parameters $0<k\le1$ for which the stable sequence in Layman's ratio-determined insertion process satisfies no recurrence $a_{n+2D}=C a_{n+D}-a_n$ with positive integers $C,D$. **The set $\mathcal E$ is uncountable and has Hausdorff dimension zero.** In particular the recurrence holds for Lebesgue-almost every insertion ratio. The argument below uses the [rotation-number classification](InverseLift.md) and the general insertion successor formula credited there. [Original conjecture C.1](https://personal.math.vt.edu/layman/sequences/ins_seq.htm)

## Digits of a finite orbit

Fix $m\ge1$ and $0\le c\le1$, with $k=1/(m+1-c)$. Write $f$ for the ratio map on $[0,1)$, $F$ for its nondecreasing degree-one lift, and $\alpha$ for its high-digit frequency. A low step $e=0$ applies $U_0(x)=1/(m+1-x)$, a high step $e=1$ applies $U_1(x)=1/(m+2-x)$. Precisely, $e=1$ when $x\ge c$. The lift records high steps by integral increments, so the number of high steps along the first $t$ iterates of an initial $x\in[0,1)$ is $\lfloor F^t(x)\rfloor$. For a general real starting point $y$, subtract $\lfloor y\rfloor$ from $\lfloor F^t(y)\rfloor$.

Consider only $\alpha$ irrational. The reference orbit from 0 has $\lfloor F^t(0)\rfloor=\lfloor t\alpha\rfloor$ for each $t\ge1$. Because $0\le x<1$ and $F^t(1)=F^t(0)+1$, the number of high steps along any orbit segment of length $t$ is either $\lfloor t\alpha\rfloor$ or $\lceil t\alpha\rceil$. This applies equally to a segment whose initial point equals the threshold, using the stated high-at-equality convention.

For a given orbit segment of length $n$, let $s_i$ be the number of high steps in its first $i$ steps, including $s_0=0$. For each $0\le i<j\le n$, the preceding bound for the segment of length $j-i$ gives
$$
-1 < (s_j-j\alpha)-(s_i-i\alpha)<1 .
$$
Taking $\beta=\max_{0\le i\le n}(s_i-i\alpha)$ shows $0\le\beta<1$ and
$$
s_i=\lfloor i\alpha+\beta\rfloor\qquad(0\le i\le n).
$$
Thus all possible digit words across all irrational rotations and all starting points lie in the list obtained from this floor formula. There are $O(n^4)$ such words: in the $(\alpha,\beta)$ unit square the possible boundaries $i\alpha+\beta=j$, $1\le i\le n$, integer $j$, give $O(n^2)$ lines. An arrangement of $L$ lines has $O(L^2)$ faces of all dimensions, since each pair has at most one crossing and each line is cut into at most $L$ intervals. On the relative interior of each face every floor is constant. Including faces on the lines and their intersections covers exact equalities too.

## Exponentially small intervals

If $\alpha$ is irrational, $0<c<1$ and the threshold $c$ has a chain of $n$ successive preimages under $f$ for every $n$. Otherwise the full set of its preimages would be finite (each point has at most one preimage since the two branch images are disjoint and each branch is injective). Cutting the interval at 0 and these finitely many points, treating each cut as a singleton, gives finitely many atoms. Each open atom lies in one branch, and its image is a connected interval avoiding every cut since all preimages of cuts are cuts and 0 has no preimage. Thus each atom determines its next atom, and the orbit of 0 has an eventually periodic digit word. This would make $\alpha$ rational.

For a fixed $n$ take such a chain $x_{-n},\ldots,x_{-1},x_0=c$, with $f(x_{i-1})=x_i$. Read the digits in **forward time**, starting at $x_{-n}$, to obtain $e_1,\ldots,e_n$. Then
$$
c\ \in\ U_{e_n}\circ\cdots\circ U_{e_1}([0,1]).
$$
This uses full closed branch extensions to cover possible endpoints. The rightmost function in the composition acts first. The count of available forward words already bounds the number of compositions; a second, independently chosen reversed word is unnecessary.

Both extensions map $[0,1]$ into itself. Their Lipschitz constants are at most $1/m^2$ and $1/(m+1)^2$, respectively, because $U_e'(x)=1/(m+1+e-x)^2$. In particular every high digit contracts by at least a factor of four in length and low steps never increase length, including $m=1$. For fixed $h\ge2$, restrict to parameters with $\alpha\ge 1/h$. Each length-$n$ word then contains at least $\lfloor n/h\rfloor$ high digits. For **each** $n$ the exceptional thresholds with this fixed $m,h$ thus admit a cover by $O(n^4)$ intervals of diameter at most $4^{-\lfloor n/h\rfloor}$. For any real $s>0$ the sum of their $s$th powers tends to 0. The $s$-dimensional Hausdorff measure is therefore zero for every $s>0$.

The map from $c$ to $k=1/(m+1-c)$ is Lipschitz on each fixed band, since its derivative is at most $1/m^2$. Taking the countable union over $m\ge1$ and $h\ge2$ covers all exceptional $k$: the classification identifies them exactly with irrational $\alpha\in(0,1)$, and each such $\alpha$ exceeds $1/h$ for some $h$. Their Hausdorff dimension is zero. Finally the continuous frequency map on even one band, for instance $m=2$, takes every irrational value in $(0,1)$, proving uncountability.

This written proof gives a size estimate for the exceptional set. It has no Lean verdict or established historical priority.

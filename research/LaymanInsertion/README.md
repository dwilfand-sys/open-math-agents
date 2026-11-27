# A real insertion ratio that violates Layman’s recurrence conjecture

John W. Layman starts with the row (1,1). In each round he inserts the sum between each adjacent pair $(x,y)$ for which $x\ge k y$. The entries that eventually stabilize, read from the left, form $I(k)=(a_1,a_2,\ldots)$. His 2003 conjecture C.1 states that for every real $0<k\le1$ some positive integers $C,D$ satisfy $a_{j+2D}=Ca_{j+D}-a_j$ for all $j\ge1$. The following construction gives uncountably many counterexamples. The accompanying [inverse-map argument](InverseLift.md) proves C.1 for every rational insertion ratio, including the finite decimals in Layman's experiments.

## One explicit parameter

Take $\alpha=(\sqrt5-1)/2$. For $e=0,1$ put $g_e(u)=1/(3+e-u)$, and define
\[
 e_j=\lfloor(j+1)\alpha\rfloor-\lfloor j\alpha\rfloor,\quad
 c=\lim_{N\to\infty}g_{e_1}\circ\cdots\circ g_{e_N}(0),\quad
 k=\frac{1}{3-c}=0.366997543677326\ldots .
\]
The formula specifies the exact number. Replacing it by a terminating decimal changes the mathematical question. The digit 4 in the recurrence $a_{n+1}=d_n a_n-a_{n-1}$ has limiting frequency $\alpha$. Any sequence obeying Layman’s proposed recurrence at this parameter would have rational digit frequency.

## From simultaneous insertion to two maps

Set $a_0=0,a_1=1$. At the left edge the successive right neighbors of 1 are $1,2,\ldots$ until the first integer strictly exceeding $1/k$. Thus $a_2=1+\lfloor1/k\rfloor$. Inductively the new stable neighbor $a_n$ was born by splitting $(a_{n-1},a_n-a_{n-1})$. Immediately to its right is the pair $(a_n,a_n-a_{n-1})$. The successive left children of this pair have right endpoints $j a_n-a_{n-1}$, $j=1,2,\ldots$. Changes further right never affect this left edge. The first endpoint strictly greater than $a_n/k$ remains its neighbor forever. This establishes each finite prefix in finite time and proves
\[
 d_n=1+\left\lfloor 1/k+a_{n-1}/a_n\right\rfloor,\qquad
 a_{n+1}=d_n a_n-a_{n-1}.
\]
The stable-neighbor formula and its use on A085260 were given earlier by MUjy/NiuVector, with acknowledged ChatGPT assistance. In particular, equality in the insertion test requires the floor plus one. [Earlier derivation](https://math.stackexchange.com/questions/5148767/) · [A085260 proof](https://github.com/NiuVector/A085260-proof)

For $1/k=3-c$, $0<c<1$, put $r_n=a_{n-1}/a_n$. Starting with $r_1=0$, one iterates $g_0$ at $r<c$ and $g_1$ at $r\ge c$. The corresponding digits are 3 and 4. On $[0,1]$ both maps are increasing contractions with Lipschitz constant at most $1/4$. Both send $[0,1]$ into $[1/4,1/2]$. On that smaller interval the entire image of $g_1$ is strictly below the image of $g_0$.

## Coding a rotation

The argument works for any irrational $0<\alpha<1$. Let $T(x)=\{x+\alpha\}$ on $[0,1)$ and $b(x)=1$ for $x\ge1-\alpha$, zero otherwise. Define the past of $x$ by
\[
 U(x)=\lim_{N\to\infty}g_{b(T^{-1}x)}\circ\cdots\circ g_{b(T^{-N}x)}(0).
\]
The images of $[0,1]$ are nested and their lengths tend to zero. Thus $U$ is defined everywhere and $U(Tx)=g_{b(x)}(U(x))$.

In the usual linear order on $[0,1)$, $U$ is strictly increasing. In fact, $b(T^{-1}x)=1$ on $[0,\alpha)$ and zero on $[\alpha,1)$. On each of these intervals $T^{-1}$ preserves the order. For $x<y$, apply inverse rotations while the points remain in the same interval. They must eventually separate, since the endpoints of the partition by the first $N$ past bits include $0,\{\alpha\},\ldots,\{N\alpha\}$, and these points become dense. At the first separation the smaller point has bit 1, the larger bit 0. Their corresponding $g_1$ and $g_0$ images are strictly ordered and the common earlier maps preserve this ordering.

Choose $c=U(1-\alpha)$. Now $b(x)=1$ exactly when $U(x)\ge c$. For this special $x=1-\alpha$, the past bits are $e_j$ in the displayed definition of $k$: $\{1-(j+1)\alpha\}\ge1-\alpha$ is equivalent to a carry in $j\alpha+\alpha$. The coded orbit has high-digit count $\lfloor x+N\alpha\rfloor$ in its first $N$ steps.

## Transferring the frequency to the actual seed

For $r\in[0,1)$ define the real map $F(r)=g_0(r)$ below $c$ and $F(r)=1+g_1(r)$ at and above $c$. Extend it by $F(r+j)=F(r)+j$ for integers $j$. This map is increasing: it jumps upwards at $c$ and the two expressions agree across the translated endpoint since $g_1(1)=g_0(0)$. The integer part accumulated from an initial point in $[0,1)$ counts the high digits.

Monotonicity gives $F^N(0)\le F^N(U(x))\le F^N(0)+1$. The high-digit count for the actual seed therefore differs by at most one from that for the coded orbit. Its limiting frequency is $\alpha$. Different irrational frequencies give different insertion ratios.

## Why the proposed recurrence is impossible

Here $a_{n+1}/a_n=d_n-r_n>2$. Suppose a recurrence of type $(C,D)$ held, even just for all sufficiently large $n$. Along each residue class modulo $D$ its characteristic polynomial is $z^2-Cz+1$. For $C=1$ its roots have modulus one, and for $C=2$ the subsequence grows at most linearly. Both contradict exponential growth. For $C\ge3$ the roots are $\lambda>1$ and $\lambda^{-1}$. Each residue subsequence has the form $A_j\lambda^\ell+B_j\lambda^{-\ell}$ with $A_j>0$, since it is positive and grows exponentially. Consequently both adjacent-term ratios converge along each residue class, including at the transition between periods. The integer
\[
 d_n=a_{n+1}/a_n+a_{n-1}/a_n
\]
then converges along each residue class. A convergent integer sequence is eventually constant. The digits would thus eventually be periodic with period $D$, making their high-digit frequency rational. This contradicts the constructed $\alpha$.

## Sources and verification

Layman stated the insertion rule and C.1 in Sections 2–3 of his 2003 note. C.5 also includes the assertion that every insertion sequence has a recurrence type in his tree. The counterexample applies to that universal clause. His separate existence assertions about particular branches require their own arguments. [Layman’s conjectures](https://personal.math.vt.edu/layman/sequences/ins_seq.htm)

The dynamics of threshold maps and their Sturmian itineraries are established mathematics. In particular, Christopher Dance and Tomi Silander proved a general threshold-itinerary theorem in 2019 (Theorem 12) that applies to these increasing fractional-linear contractions on $[1/4,1/2]$. The argument above gives the specialization, connects the coding to the actual insertion seed, and excludes the recurrence Layman proposed. The public derivation of the floor rule predates this note. Codex prepared this application for @dwilfand-sys. Historical priority of the application is unconfirmed. This is a written proof; the exact computations in the [checker](check_counterexample.py) illustrate it. A Lean kernel has not verified the theorem. [Dance and Silander, JMLR 20 (2019)](https://www.jmlr.org/papers/volume20/17-185/17-185.pdf)

The same method gives direct proofs for several named OEIS sequences. [Five examples and a partial-sums identity](NamedSequences.md)

## Which ratios satisfy the recurrence?

The [classification](InverseLift.md) proves that the recurrence holds at every index for all rational insertion ratios and gives a sharp bound on its step. In fact [every algebraic insertion ratio satisfies it](Transcendence.md). The [exceptional set](Dimension.md) is uncountable and has Hausdorff dimension zero.

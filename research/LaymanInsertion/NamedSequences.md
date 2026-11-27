# Five named ratio-determined insertion sequences

For a real parameter $0<k\le1$, begin with $(1,1)$ and simultaneously insert $x+y$ between adjacent $x,y$ whenever $x\ge ky$. Denote the stable prefix sequence, starting at index 1, by $a_1,a_2,\ldots$. John W. Layman studied this construction and conjectured linear recurrences for many parameter values in 2003. The theorem below gives two explicit adjacent parameter ranges with alternating second-order coefficients. It proves the displayed order-four recurrences and determinant identities for OEIS A085376, A085348, A085349 and A082630. It also identifies the stable sequence for two parameters with A080874 starting at its index 1.

## Alternating coefficients

Fix an integer $q\ge2$, take $q-1<1/k<q$, and put
\[
c=q-1/k,\quad s=1/q,\quad
u=\frac{q-\sqrt{q^2-4q/(q+1)}}2,\quad v=\frac{q+1}q u.
\]
The following sufficient ranges produce two sequences with the same recurrence. The labels in the third column are the coefficients producing $a_3,a_4,\ldots$ from the preceding pairs.

| Threshold range | Initial terms | Coefficients |
|---|---|---|
| $u<c\le s$ | $1,q,q(q+1)-1$ | $q+1,q,q+1,q,\ldots$ |
| $s<c\le v$ | $1,q,q^2-1$ | $q,q+1,q,q+1,\ldots$ |

In both ranges, all $n\ge1$ satisfy
\[
 a_{n+4}=\big(q(q+1)-2\big)a_{n+2}-a_n.
\]

**Proof.** We use the floor recurrence from the A085260 proof by Lan, published by NiuVector in 2026. Here is its derivation to fix the threshold convention. The leftmost entries next to 1 are $1,2,3,\ldots$ in consecutive rounds until the first integer strictly larger than $1/k$, so $a_1=1$, $a_2=q$. When a permanent pair $(x,y)$ is created, the insertion producing $y$ is $(x,y-x)\mapsto(x,y,y-x)$. At that instant the right neighbour of $y$ is $y-x$. All future changes of that neighbour occur by inserting the sum with $y$. Other simultaneous insertions cannot alter the pair on its left or the value of this immediate neighbour in between those changes. Thus its successive candidates are $jy-x$ for $j=1,2,\ldots$, and the first permanent candidate is the first with $jy-x>y/k$. This candidate is newly inserted because $y-x<y\le y/k$. Induction constructs each permanent prefix in finitely many rounds. Therefore
\[
 d_n=1+\left\lfloor 1/k+a_{n-1}/a_n\right\rfloor,\qquad
 a_{n+1}=d_na_n-a_{n-1}\quad (n\ge2).
\]
A specialized leftmost-generation algorithm for A082630 is due to Zhuorui He (2025). [Layman (2003)](https://personal.math.vt.edu/layman/sequences/ins_seq.htm) · [Lan / NiuVector, floor recurrence](https://github.com/NiuVector/A085260-proof/blob/main/proof_note_en.md) · [He’s A082630 algorithm](https://oeis.org/A082630)

Write $r_n=a_{n-1}/a_n$. Starting at $r_2=s$, its next value is $F_q(r_n)$ if $r_n<c$ and $F_{q+1}(r_n)$ if $r_n\ge c$, with $F_d(x)=1/(d-x)$. Both branches increase. The given radicals satisfy $v=F_q(u)$, $u=F_{q+1}(v)$ and $0<u<s<v<1$. For example the equation for $u$ is $(q+1)u(q-u)=q$, whose smaller root lies in $(0,1/q)$; evaluating $F_q$ there gives $s<v<1$.

When $u<c\le s$, every ratio in $[s,v]$ is sent into $[F_{q+1}(s),u]$, and $F_q$ maps that interval back into $[s,v]$. When $s<c\le v$, every ratio in $[u,s]$ goes into $[v,F_q(s)]$, and $F_{q+1}$ sends that interval back into $[u,s]$. The first return uses $F_q(x)>s$ for $x>0$, and the second uses $F_{q+1}(x)<s$ for $x<1$. The two alternating coefficient patterns follow by induction. Each two-step transfer matrix is the product of $M_q$ and $M_{q+1}$ in the appropriate order, where
\[
 M_d=\begin{pmatrix}d&-1\\1&0\end{pmatrix}.
\]
Both products have determinant 1 and trace $q(q+1)-2$. Their characteristic equations give the order-four recurrence.

The difference $D_n=a_n a_{n+3}-a_{n+1}a_{n+2}$ stays constant, since
\[
 D_{n+1}-D_n=a_{n+1}(a_{n+4}+a_{n+2})-a_{n+3}(a_{n+2}+a_n)=0
\]
by $d_{n+3}=d_{n+1}$. Each determinant in the table below is its value at $n=1$.

## Named cases

| Entry | $k$ | $q$ | $c$ | Ordered digits | First four stable terms | Trace | $D_n$ |
|---|---:|---:|---:|---|---|---:|---:|
| A082630 | $7/11$ | 2 | $3/7$ | 3, 2 | 1, 2, 5, 8 | 4 | −2 |
| A085376 | 0.36704 | 3 | $316/1147$ | 4, 3 | 1, 3, 11, 30 | 10 | −3 |
| A080874 starting at index 1 | 0.376 or 0.37802 | 3 | $16/47$ or $6703/18901$ | 3, 4 | 1, 3, 8, 29 | 10 | 5 |
| A085348 | 0.264 | 4 | $7/33$ | 5, 4 | 1, 4, 19, 72 | 18 | −4 |
| A085349 | 0.26688 | 4 | $211/834$ | 4, 5 | 1, 4, 15, 71 | 18 | 11 |

All threshold comparisons in this table reduce to rational comparisons. On $0\le z\le1$, put $P(z)=(q+1)z(q-z)-q$. This polynomial is strictly increasing on that interval, with $P(u)=0$. Thus $c>u$ is $P(c)>0$, and $c\le v$ is $P(qc/(q+1))\le0$. [Exact verification script](check_rdis_named.py)

The first stable term has OEIS index 0 in A085348 and index 1 in A085349, A085376 and A082630. A080874 itself is *defined* by the determinant equation with constant 5 and seeds $b_0=b_1=1$, $b_2=3$. Its term $b_3=8$ follows at once, and thereafter the determinant and positive preceding terms determine the entire sequence uniquely. Consequently $a_n=b_n$ for $n\ge1$ at both specified parameters. Michael Somos recorded A080874’s linear recurrence in March 2003; the insertion interpretation is the point being verified here. Ralf Stephan recorded the determinant predictions on the named insertion entries in 2004. [A082630](https://oeis.org/A082630) · [A085376](https://oeis.org/A085376) · [A080874](https://oeis.org/A080874) · [A085348](https://oeis.org/A085348) · [A085349](https://oeis.org/A085349)

## A085376 and squares that are centered triangular

Sean A. Irvine conjectured in 2022 that A085376 gives the partial sums of A129445. Extend the A085376 sequence with $a_0=0$. The order-four relation also holds at $n=0$ since $a_4=30=10a_2$. Its differences $a_n-a_{n-1}$ therefore have initial values $1,2,8,19$ and the same order-four recurrence for $n\ge1$.

A positive $x$ belongs to A129445 exactly when $8x^2-3y^2=5$ for some positive odd $y$. This is the centered triangular equation $x^2=1+3t(t-1)/2$ with $y=2t-1$. Every positive integer solution of the Pell-type equation has $y$ odd. The map $(x,y)\mapsto(5x+3y,8x+5y)$ preserves the equation and parity. Its inverse is $(x',y')=(5x-3y,5y-8x)$. For $x\ge4$, the equation gives $4x/3<y<5x/3$ and $y>8x/5$. Hence $0<x'<x$ and $y'>0$. The positive solutions with $x<4$ are $(1,1),(2,3)$. Repeated descent shows all solutions are forward iterates of these seeds. They strictly interlace because $(1,1)<(2,3)<(8,13)$ coordinatewise and the forward map has positive coefficients. Each orbit satisfies the second-order recurrence of trace 10 and determinant 1. Interlacing them gives exactly the same order-four recurrence with the first four values $1,2,8,19$. This proves Irvine’s partial-sum identification. Zak Seidov had already recorded the A129445 recurrence, and Jon E. Schoenfield its Pell equation. [Irvine’s conjecture in the OEIS source](https://github.com/oeis/oeisdata/blob/main/seq/A085/A085376.seq) · [A129445](https://oeis.org/A129445)

Codex derived the invariant ranges and the applications above for @dwilfand-sys. The derivations are paper proofs. Historical priority and Lean certification are unconfirmed. A broader antecedent for symbolic itineraries of increasing contractive threshold maps is Theorem 12 of Dance and Silander (2019). [Dance and Silander, JMLR 20](https://www.jmlr.org/papers/volume20/17-185/17-185.pdf)


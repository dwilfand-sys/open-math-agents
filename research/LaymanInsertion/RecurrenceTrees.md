# Which of Layman's recurrence-tree predictions hold?

John W. Layman defined a ratio-determined insertion sequence \(I(k)\) for every real \(0<k\le1\) and called \((C,D)\) a recurrence type whenever \(a_{j+2D}=C a_{j+D}-a_j\) for all \(j\ge1\). This definition allows one sequence to have several types. His C.5 makes two assertions, existence in the parameter intervals prescribed by the tree and coverage of all insertion sequences. Every node of each tree with initial traces \(s,s+1\), \(s\ge2\), has a rational insertion parameter strictly between those of its parents. Every insertion sequence that satisfies any such recurrence has a type in one of these trees. Sequences with irrational digit frequency disprove the assertion of coverage for all real parameters. [Layman, *Ratio-Determined Insertion Sequences and the Tree of their Recurrence Types* (2003), §§3–4](https://personal.math.vt.edu/layman/sequences/ins_seq.htm) · [Proof of the frequency classification](InverseLift.md)

## Frequency and the two possible words

Set \(a_0=0,\ a_1=1\). Introduce one band at a time by
\[
s\ge2,\qquad 1/k=s-c,\qquad 0\le c\le1 .
\]
The floor update is \(a_{n+1}=d_na_n-a_{n-1}\), where \(d_n=1+\lfloor 1/k+a_{n-1}/a_n\rfloor\). Write \(r_n=a_{n-1}/a_n\). Then \(d_n=s\) for \(r_n<c\), and \(d_n=s+1\) for \(r_n\ge c\). In either case \(r_{n+1}=1/(d_n-r_n)\). The insertion inequality includes equality, accounting for the choice of the high digit at the threshold. The floor update was previously derived by Lan. [NiuVector, proof note for A085260](https://github.com/NiuVector/A085260-proof/blob/main/proof_note_en.md)

Let \(\alpha(c)\) denote the limiting frequency of the high digit, starting from \(r_1=0\). The continuous-inverse argument proves that \(\alpha\) is continuous from \([0,1]\) onto \([0,1]\), that \(\alpha(0)=1,\ \alpha(1)=0\), and that the limiting rotation displacement is independent of the starting point. It is also nonincreasing. Indeed the degree-one lift \(F_c(x)=1/(s-x)\) for \(0\le x<c\), \(F_c(x)=1+1/(s+1-x)\) for \(c\le x<1\), is increasing in \(x\) and nonincreasing in \(c\). Ordered lifts have ordered iterates and hence ordered limiting displacements. As \(k=1/(s-c)\) increases, so does \(c\). Any choices of parameters realizing distinct ordered frequencies within this band therefore occur in strictly reversed order. [Continuous inverse, including the parabolic band \(s=2\)](InverseLift.md)

For \(\alpha=p/q\) in lowest terms, put
\[
W_{p/q}(i)=\lfloor ip/q\rfloor-\lfloor(i-1)p/q\rfloor,
\qquad 1\le i\le q.
\]
The same argument gives the following precise initial-point statement. If \(h_n\) counts high digits among \(d_1,\ldots,d_n\), then for all \(n\ge1\) either \(h_n=\lfloor n\alpha\rfloor\) throughout or \(h_n=\lceil n\alpha\rceil-1\) throughout. Thus from \(d_2\) on, the period is the word \(W_{p/q}\), interpreted as digits \(s,s+1\), up to cyclic shift. Indeed for \(0<p<q\) one has \(\lceil ip/q\rceil=\lfloor(ip+q-1)/q\rfloor\), and \(tp\equiv q-1\bmod q\) has a solution. The endpoint words are the constant words \(0\) and \(1\), of length one.

## The matrices reproduce the tree

For \(M_d=\left(\begin{smallmatrix}d&-1\\1&0\end{smallmatrix}\right)\) let \(T(W)\) be the product of the corresponding matrices in reverse reading order. Thus \(T(UV)=T(V)T(U)\), the order arising when one advances the state \((a_{n+1},a_n)^t\). The trace is unchanged by cyclic shifts. If the high frequency is \(p/q\), the product covering the next \(q\) steps from this state has trace \(\operatorname{tr}T(W_{p/q})\) and determinant one. The next \(q\) steps repeat that product. Cayley–Hamilton on the second coordinate gives the recurrence
\[
a_{j+2q}=\operatorname{tr}T(W_{p/q})\,a_{j+q}-a_j\qquad(j\ge1).
\]
This use of \(d_2\) onward covers the very first required identity.

For Farey neighbors \(p/q<r/t\) with \(qr-pt=1\), the mediant word is the concatenation \(W_{p/q}W_{r/t}\). This is the standard factorization of lower Christoffel words with \(p\) ones in a word of length \(q\). For the floor convention above the check is direct. Put \(P=p+r,Q=q+t\). For \(0\le j\le q\),
\[
\frac{jP}{Q}-\frac{jp}{q}=\frac{j}{qQ}<\frac1q .
\]
For \(0\le i\le t\),
\[
\frac{(q+i)P}{Q}-\left(p+\frac{ir}{t}\right)=\frac{t-i}{tQ}<\frac1t .
\]
Both differences are nonnegative, and the reference terms have respective denominators dividing \(q,t\), so the floors coincide. Taking successive differences proves concatenation, including both endpoints. [Jean Berstel, Aaron Lauve, Christophe Reutenauer and Franco Saliola, *Combinatorics on Words*, §§3.1–3.2, including the Borel–Laubie factorization theorem](https://webpages.math.luc.edu/~lauve/papers/wordsbook.pdf)

At \(0/1,1/1\) the endpoint labels are \((s,1),(s+1,1)\). Their first child has label \((s(s+1)-2,2)\). In general write \(A=T(U)\), \(B=T(V)\) for a pair of parent words. Their child has matrix \(BA\). The new neighboring child words \(UUV\) and \(UVV\) have matrices \(BA^2\) and \(B^2A\). Cayley–Hamilton for \(A\) and \(B\) gives
\[
\begin{aligned}
\operatorname{tr}(BA^2)&=\operatorname{tr}(A)\operatorname{tr}(BA)-\operatorname{tr}(B),\\
\operatorname{tr}(B^2A)&=\operatorname{tr}(B)\operatorname{tr}(BA)-\operatorname{tr}(A).
\end{aligned}
\]
Lengths add at each concatenation. These are exactly Layman's \(LR-X\) and \(l+r\) rules. Every node consequently has the trace and denominator of its own reduced frequency \(p/q\). Surjectivity gives a parameter for it. Its frequency is strictly between its parents', so monotonicity places its parameter strictly between theirs. Conversely every reduced rational in \([0,1]\) occurs in the Stern–Brocot subdivision of that interval. The rational-frequency classification therefore places a recurrence type of every recurring \(I(k)\) in one of the trees. Every rational \(k\) falls in this class. The real parameters with irrational frequency supply the exceptions.

### Every interior node admits rational parameters

Start with one parameter given by continuity for \(0<p/q<1\). The digit tail from \(d_2\) on has period \(q\). Let \(f_d(x)=1/(d-x)\) for \(x\in[0,1]\). The branch \(f_s\) is 1-Lipschitz and \(f_{s+1}\) is at most \(1/s^2\)-Lipschitz. Since every period contains a high digit, iterates converge along its \(q\) phases to points \(x_i\) constituting a periodic orbit for the prescribed branch maps. These limiting points belong to \((0,1)\). Both maps are positive, the high branch sends \([0,1]\) strictly below 1, and each following low branch sends points below 1 to points below 1.

The \(q\) points are distinct. For any point of the cycle, its preceding digit is uniquely recovered by testing whether the point is greater than \(1/s\) (low predecessor) or less than \(1/s\) (high predecessor), since every predecessor lies strictly between 0 and 1. Each branch is injective, so equality of two phase points forces equality of the entire backwards digit words at those phases. A period \(q\) word with \(p\) ones and \(\gcd(p,q)=1\) has least period \(q\). Thus the phases must coincide.

Each \(x_i\) with low outgoing digit is \(\le c\), and each with high outgoing digit is \(\ge c\), by passage to a subsequential limit in its threshold comparison. Distinctness gives
\[
 \max_{\text{low outgoing}}x_i < \min_{\text{high outgoing}}x_i.
\]
At every cutoff \(c'\) strictly between these extremes the same \(q\) points form an actual threshold-map cycle, with \(p\) high digits. Its lift advances by \(p\) in \(q\) steps. Since the rotation frequency is independent of the starting point, the original orbit from zero also has frequency \(p/q\). This open interval contains a rational \(c'\), giving a rational \(k'=1/(s-c')\). Parent fibers remain strictly ordered. The two endpoint parameters, \(1/(s-1)\) and \(1/s\), are rational as well.

### Two sequences at each interior rational frequency

There are exactly two distinct original sequences for a fixed band \(s\) and a fixed reduced frequency \(0<p/q<1\). They share their first \(q\) terms, differ in term \(q+1\), and both have least recurrence step \(q\). This establishes a version of the twin phenomenon indexed by frequency.

For \(n<q\), \(np/q\) is nonintegral when \(n>0\). The first \(q-1\) floor counts are therefore the same on both sides of \(p/q\) for all sufficiently close irrational frequencies, and also at \(p/q\) itself. They determine a common rational ratio \(z=r_q\) because \(r_1=0\) and all branch maps preserve rationality. At an irrational frequency just above \(p/q\) the count \(h_q\) is \(p\), so step \(q\) uses the high digit and its cutoff satisfies \(c\le z\). At an irrational frequency just below \(p/q\), \(h_q=p-1\), so it uses the low digit and \(c>z\). By monotonicity, \(\alpha(z)\) lies between any such lower and upper frequencies. Hence \(\alpha(z)=p/q\).

Take the cycle obtained above for this cutoff \(z\). Every phase point is irrational. Indeed if one were a reduced fraction \(u/v\) with \(0<u<v\), its predecessor \(d-v/u\) would have denominator at most \(u<v\). Going backwards around the cycle gives an impossible strict descent of positive integer denominators. The rational \(z\) therefore lies strictly between the maximum low and minimum high phase points. Take rational cutoffs on both sides of \(z\) in that interval. Both have frequency \(p/q\) and the same first \(q-1\) digits, but at step \(q\) they make opposite choices, hence have different \(a_{q+1}\). The two formulae for \(h_n\) permit at most two whole sequences.

Positive high frequency gives exponential growth, so any recurrence of step \(D\) forces the integer digits to be eventually \(D\)-periodic by the characteristic-root argument. Their frequency is then an integer divided by \(D\), so \(q\mid D\). The Cayley–Hamilton construction already gives step \(q\), proving minimality. Two sequences per frequency do not by themselves count all sequences satisfying a given numerical pair \((C,D)\); Layman defined that type without a minimality restriction. [Characteristic-root argument](InverseLift.md)

## The original indexing and the twin claim

**C.2.** At \(k=1/t\) for every integer \(t\ge1\), the digit is \(t+1\), since \(0\le r_n<1\). Taking \(t=m+1\) gives type \((m+2,1)\). The printed coefficient \(m+1\) is off by one. A positive sequence cannot satisfy both adjacent-step identities with different coefficients.

**C.3.** Layman's definition immediately before C.2 permits every satisfied recurrence. At \(k=1/2\) the sequence starts \(1,3,8,21,\ldots\) with all digits 3. At \(k=3/5\), it starts \(1,2,5,13,\ldots\). Here \(d_1=2\) and \(r_2=1/2\) exceeds the cutoff \(1/3\). The high branch \(x\mapsto1/(3-x)\) preserves \([1/3,1)\), so \(d_n=3\) for \(n\ge2\). Both sequences satisfy \((3,1)\); squaring its determinant-one matrix gives \((7,2)\) for both. They differ in term two. C.3 predicts that any two distinct sequences of this type agree through term two. This also refutes the combination of its exact-count and prefix assertions even if further sequences have the same type.

Even imposing the least possible step cannot rescue the claimed twin count in full. A sequence of type \((2,1)\) is an increasing arithmetic progression, so \(r_n\to1\). For \(n\ge2\) its update digit must be 2, hence \(1/k+r_n<2\). Passing to the limit gives \(k\ge1\), and the allowed interval forces \(k=1\). This parameter produces \(a_n=n\). Thus \((2,1)\), of least step one, occurs for exactly one insertion sequence.

For each \(C\ge3\), however, \((C,1)\) has exactly two insertion sequences. Its recurrence forces \(d_n=C\) from \(n=2\). If \(B=a_2=1+\lfloor 1/k\rfloor\), then each \(d_n\) lies in \(\{B,B+1\}\), so \(B\) is either \(C\) or \(C-1\) and the entire sequence is determined. The value \(B=C\) is realized at \(k=1/(C-1)\). To realize \(B=C-1\), take \(s=C-1\) and any \(0<c<1/C\). Then \(r_1=0<c\) selects the low first digit, \(r_2=1/s>c\), and every subsequent high step sends the ratio above \(1/C\). This realizes the other sequence.

**C.4.** On \(1/m<k<1/(m-1)\) the digits are \(m,m+1\). The explicit choice \(k=m/(m^2-1)\) has cutoff \(c=1/m\). Each low step sends its ratio to at least \(1/m\), each high step sends it strictly below \(1/m\), and \(r_1=0\) starts on the low side. The digits alternate from the beginning and their two-step trace is \(m(m+1)-2\). This holds for every \(m\ge2\) and gives the coefficient in Layman's example.

In fact his printed coefficient \(m(m-1)-2\) is impossible throughout the stated interval. Eliminating the intermediate terms in the single-step identities gives, at every \(j\ge1\),
\[
\frac{a_{j+4}+a_j}{a_{j+2}}
=d_{j+3}d_{j+2}-2+(d_{j+1}-d_{j+3})r_{j+2}.
\]
If \(d_{j+3}=m\) the right-hand side is at least \(m^2-2\). If \(d_{j+3}=m+1\) it is at least \(m(m+1)-2-r_{j+2}>m^2-2\). In either case it exceeds the printed number.

**C.5's endpoint convention.** The tree following C.4 uses initial traces \(m-1,m\); its valid range is \(m\ge3\), giving \(s=m-1\) above. Its displayed example starts at \(2,3\), corresponding to \(k=1,1/2\). The formal \(m=2\) tree starts with \((1,1),(2,1)\) and gives \((0,2)\) as first child. The first endpoint is impossible for positive increasing terms, and the child even violates the stipulated positivity of \(C\). Thus this degenerate tree is excluded by the original definitions themselves.

Codex prepared these arguments for @dwilfand-sys. Layman posed the conjectures and gave the numerical tree, Lan derived the floor update, and the Christoffel factorization is classical. These are paper arguments. Historical priority and Lean certification remain unconfirmed.

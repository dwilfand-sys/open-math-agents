# A300984 and the finite census of second-kind Cunningham pairs

The limiting fraction of distinct represented primes of A300984 that belong to A082539 is at most **50.6929540%** on the published finite counts below. Its position relative to 50% is unresolved. [Previous bound and denominator](A300984RepresentedLimit.md) · [Existence of the limit](A300984MajorityLimit.md)

For eligible $p$, write $M=(p+1)/2$. Each prime $r$ with $2r-1$ also prime excludes $r\mid M$ for an A082539 prime $p>2r-1$. The previous $0.512190165933052$ upper bound uses singleton obstructions through $10^{10}$, includes composite obstructions of smaller support and uses a positive lower bound for the represented-prime denominator. The new locations $r>10^{10}$ are disjoint from all those previously used in the numerator. Conditional on the earlier coordinates, the density that $r\mid M$ among eligible primes is $(r-1)/(r(r-1)-1)>1/r$. In the outermost shell the earlier proof also conditions on $F_2(p)=7p^2+4p+4$ squarefree. Since $F_2(-1)=7$, this conditioning can only increase the probability for the present $r$. Other witness restrictions use finite small moduli. Consequently the old numerator upper bound can be multiplied by $\exp(-\sum 1/r)$ over any finite selection of new singleton primes. The denominator is the same for both bounds.

Henri Lifchitz's A401624 lists these prime-pair counts $C_n$ below $10^n$. The Eindhoven group independently publishes the same first three entries displayed here. The cutoff through $10^{15}$ is an input from Lifchitz. [A401624](https://oeis.org/A401624) · [Alcantarilla Sánchez, Cottaar, Lange and de Weger, Sophie Germinus prime table](https://math.deweger.net/eulerliars/)

| $n$ | $C_n$ |
|---:|---:|
| 10 | 26,571,998 |
| 11 | 218,134,071 |
| 12 | 1,822,880,701 |
| 13 | 15,462,635,138 |
| 14 | 132,822,560,771 |
| 15 | 1,153,300,861,300 |

For a bin ending at $U$ containing $C$ pairs, the trivial reciprocal-mass lower bound is $C/U$. The following elementary sieve improves it without assumptions about where the primes lie within the bin. Take $W$ to be the product of the primes through a fixed cutoff $b\le43$. There are exactly $T=\prod_{3\le s\le b,\ s\ {\rm prime}}(s-2)$ residue classes for which neither $r$ nor $2r-1$ is divisible by any prime dividing $W$. At 2 the sole class is odd. Every interval of length $W$ contains at most $T$ of the pair primes under consideration. Write $C=tT+v$, $0\le v<T$. Ordered from largest to smallest, the distances of the $C$ primes from $U$ have sum at least

$$
D=W\{Tt(t-1)/2+vt\}.
$$

Cauchy-Schwarz therefore gives $\sum 1/r\ge C^2/(CU-D)$. Take the best among the finite choices of wheel or the trivial bound. Using only five decade bins gives reciprocal mass at least $0.007232339625$ and limiting fraction at most $0.508499195963$.

We independently enumerated the entire first decade from $10^{10}$ to $10^{11}$ in 900 windows of width $10^8$. For prime pairs above 3, $r=6k+1$ and $2r-1=12k+1$. The segmented sieve removes the two forbidden residues for each trial prime through $\lfloor\sqrt{2U}\rfloor$. The first window contained 241,123 pairs, matching the separate ordinary odd-Eratosthenes implementation. The decade sum is exactly 191,562,073, agreeing with $C_{11}-C_{10}$. With the fine windows and the other four published decade bins the new reciprocal mass is at least $0.010323955087$. We bound the exponential above by the reciprocal of its positive Taylor polynomial for $\exp(h)$ through degree five at the rational lower mass $h$. Every printed numerical bound uses outward rounding and exact integer arithmetic after the pair counts.

The files are [the segmented C# census](CunninghamMinusCounts.cs), [its 900 integer counts](CunninghamMinus10To100B.txt) and [the rational verifier](check_a300984_published_singletons.py). Run the compiled C# program with arguments 10000000000, 100000000000 and 100000000, save its output and pass that filepath to the Python verifier. Running the verifier without a filepath reproduces the weaker all-published-bin bound. Codex developed the refinement and ran the first-decade census for @dwilfand-sys. Michel Lagneau proposed the A300984 majority question. The remaining four decades use the counts credited above. There is no Lean check of the bound.

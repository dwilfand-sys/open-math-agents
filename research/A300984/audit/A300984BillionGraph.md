# A billion-divisor graph bound for the A300984 majority

The proportion of distinct represented odd primes in A082539 has limit superior at most **51.284514%**. This bound combines 16 graphs of shifted-prime divisors with the finite congruence estimates in the preceding calculations. The strict majority remains open. [Conjecture](https://oeis.org/A300984) · [Base density argument](Density.md) · [Additional linear divisors](LagneauConditionalLinear.md)

Fix the divisibility mask for the 15 free primes up to 73 used in the original sieve. If the mask is empty or has one selected small prime $t$, enlarge its graph using obstruction divisors up to $C=10^9$. Vertices are the primes $r>73$ with $2r-1$ composite. When $t$ is present require $2tr-1$ composite as well. Join two distinct vertices $r,s$ if $rs\le C$ with $2rs-1$ prime, or if $t$ is present and $trs\le C$ with $2trs-1$ prime. Either event $r,s\mid(p+1)/2$ excludes membership in A082539 except at one of finitely many $p$.

For these masks every previous one-large-prime divisor has multiplier one or $t$. The restrictions on vertices therefore omit the support of all independently applied singleton and linear rules. Conditional on the fixed mask and those rules, the remaining vertex indicators stay independent in density. Calculations on small residue classes use disjoint moduli. With or without the outermost range's conditioning on $7p^2+4p+4$ squarefree, their probabilities $x_r$ satisfy

$$
\frac1r\le x_r\le\frac1{r-1}.
$$

The local numerator is $r-1$, because $F(-1)=7$ and every vertex exceeds 73. The denominator is $r(r-1)-1-b$, where $0\le b\le2$ counts excluded unit roots.

Let $\mu$ be the sum of all edge probabilities and $\Delta$ the sum of joint probabilities over ordered pairs of distinct edges sharing a vertex. Janson's inequality bounds the probability that no edge occurs by $\exp(-\mu+\Delta/2)$. [Yufei Zhao, *Probabilistic Methods in Combinatorics*, Theorem 8.1.2](https://ocw.mit.edu/courses/18-226-probabilistic-methods-in-combinatorics-fall-2022/mit18_226_f22_lec16-17.pdf)

Set $S=10^8$, $l_r=\lfloor S/r\rfloor$ and $u_r=\lceil S/(r-1)\rceil$. The numerator for a lower bound on $\mu$ is $L=\sum_{rs}l_rl_s$ with denominator $S^2$. For each vertex $r$, let $N_r$ denote its neighbors. An upper bound on $\Delta$ has denominator $S^3$ and numerator

$$
T=\sum_r u_r\left[\left(\sum_{s\in N_r}u_s\right)^2-\sum_{s\in N_r}u_s^2\right].
$$

With $z=\max(0,L/S^2-T/(2S^3))$, the survival bound is at most $1/\sum_{j=0}^6 z^j/j!$. This last bound is rational and its stored value is rounded upwards to 15 decimal places. Take the smaller of this bound and the prior graph bound for each of these masks. Masks with two or more selected small primes use the prior estimate.

The empty mask alone has 3,078,498 edges. The normalized numerator after all 16 graph calculations, the extra linear divisors, and the range-specific witness tests is at most $0.499430749861207$. Two independent sieves find 26,469,017 prime pairs $r,2r-1$ between $20{,}000{,}000$ and $10^{10}$, with the bound applying to the first prime $r$. Their common outward-rounded multiplier is $0.979789013592184$. This leaves a represented primitive numerator of at most $0.489336761764117$ against a represented denominator of at least $0.954160870567672$. The resulting ratio is at most $0.512845136347909$.

## Reproduction

Run from the directory containing the following files. The full Python graph replay uses NumPy and independently reconstructs every counted edge total, both integer moments and the 16 outward-rounded Janson bounds. The ordinary small-instance checker evaluates exact avoidance probabilities by vertex deletion.

~~~sh
node lagneau_wide_graph.cjs 1000000000 73 Wide1B.json
python lagneau_wide_replay.py Wide1B.json
node lagneau_wide_graph.cjs 10000 73 WideSmall.json
python lagneau_wide_check.py WideSmall.json
python lagneau_extra_one_replay.py Positive1B.json
python lagneau_negative_replay.py lagneau_negative_1b.json
python lagneau_large_singletons_check.py 20000000 10000000000
node lagneau_billion_graph_bound.cjs 20000000 73 Wide1B.json Positive1B.json lagneau_negative_1b.json
~~~

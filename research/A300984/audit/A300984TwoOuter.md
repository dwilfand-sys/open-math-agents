# A finite graph of shifted-prime divisors for A300984

Among the distinct odd primes represented by A300984 terms up to $Y$, the fraction in A082539 has limit superior at most **53.655185%**. This bound uses two additional large prime factors in one divisor of $(p+1)/2$. Its numerical part uses exact integer bounds. The strict majority conjecture remains unresolved. [A300984](https://oeis.org/A300984) · [A082539](https://oeis.org/A082539)

## Counting the new obstructions

Let $p\equiv1\bmod12$ be prime with $p+1$ squarefree. Put $k=(p+1)/2$. If $d>1$ and $2d-1$ is prime, then $d\mid k$ excludes $p$ from A082539 except at the single value $p=2d-1$. A fixed finite list of such divisors bounds the limiting density from above.

The existing sieve first forbids the singleton primes $q$ for which $2q-1$ is also prime. It fixes the subset of remaining primes up to $B$ that divide $k$. For each fixed subset it then forbids any further prime for which its product with a selected small divisor gives an obstruction. Conditional on this information the remaining large-prime divisibility indicators are independent in density by the Chinese remainder theorem, the prime number theorem in arithmetic progressions and the square-divisor tail estimates in the baseline proof.

Factor every squarefree $d\le D$ with $d\equiv1\bmod6$ and $2d-1$ prime. For each $d=t r s$ with $r<s$ distinct primes exceeding $B$ and all prime factors of $t$ in the selected small subset, join $r,s$ by an edge. Skip rules already ruled out by singleton conditions and remove vertices already forbidden by the one-large-prime conditions. The event that both endpoints of any remaining edge divide $k$ certifies a further exclusion. Several divisors may yield the same edge. Such an edge occurs only once in each fixed subset.

Write $x_v$ for the local conditional probability that $v\mid k$. Normally $x_v=(v-1)/(v(v-1)-1)$. When conditioning also on $F(p)=7p^2+4p+4$ squarefree, subtract the number of reduced roots of $F$ modulo $v^2$ from the denominator. Every graph vertex exceeds seven, so $F(-1)=7$ guarantees the numerator stays $v-1$. At the baseline's fixed small prime 7 the one root in the numerator is removed explicitly there.

## A certified survival bound

For $S=10^7$, write $l_i=\lfloor Sx_i\rfloor$ and $u_i=\lceil Sx_i\rceil$. Set $L=\sum_{ij} l_i l_j$, $V=\sum_{ij}u_i u_j$, summing each undirected edge once. Let $N_i$ be the neighbor set of $i$ and put

$$
T=\sum_i u_i\left[\left(\sum_{j\in N_i}u_j\right)^2-\sum_{j\in N_i}u_j^2\right].
$$

The sum of edge-event probabilities is at least $L/S^2$. The sum of ordered intersections of disjoint edge events is at most $V^2/S^4$ by independence. For ordered adjacent events with common vertex $i$, the intersection probability is $x_i x_j x_k$. The sum over such events is at most $T/S^3$. The second Bonferroni inequality therefore bounds the probability of avoiding all edges by

$$
\min\left(1,\ 1-\frac{L}{S^2}+
 \frac12\left(\frac{V^2}{S^4}+\frac{T}{S^3}\right)\right).
$$

The code rounds its product with the previous surviving weight upwards. For subsets selecting four or more free small primes it retains the prior upper bound of one on this graph factor. This choice affects only how tight the bound is. Array sums are nonnegative integers checked within JavaScript's exact integer range, and final products, sums for $T$, and outward divisions use BigInt.

## Reproduction

Run the following in the directory containing the scripts. The independent Python check reconstructs every relevant divisor in the fixture and computes the exact edge-avoidance probability by a vertex-deletion recurrence with rational arithmetic.

~~~sh
node lagneau_two_outer.cjs 5000 19 83
python lagneau_two_outer_check.py
node lagneau_two_outer.cjs 20000000 73
~~~

| Maximum divisor $D$ | Small cutoff $B$ | Vertices | Distinct edges | Upper bound on the represented primitive fraction |
|---:|---:|---:|---:|---:|
| 10,000,000 | 61 | 7,919 | 53,931 | 0.541056928219572 |
| 20,000,000 | 61 | 14,697 | 108,463 | 0.536680012397298 |
| 20,000,000 | 73 | 12,384 | 99,543 | 0.536551848917223 |

For the final row, among eligible primes the primitive fraction has upper bound $0.533453859716221$. Conditioning also on $F(p)$ squarefree gives $0.541799691584107$. In the outside shell only $4p^2$ can represent $p$. Applying the baseline interval for the density of squarefree $F(p)$ and the shell weights gives a represented primitive numerator at most $0.511956779267551$ relative to eligible primes. The three-witness calculation gives a represented denominator at least $0.954160870567672$ relative to the same population. The table rounds the resulting ratio upwards.

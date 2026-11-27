# A300984 upper bound from extended slopes and medium prime factors

The limiting fraction of distinct represented odd primes in A300984 that belong to A082539 is at most **0.504840964546**. This uses the four high-decade census totals credited to Henri Lifchitz in the previous note and the new independently replayed computations described below. It leaves the majority conjecture unresolved. [Previous Cunningham census](A300984CunninghamCensus.md) · [Represented-prime limit and denominator](A300984RepresentedLimit.md)

Write $M=(p+1)/2$. An eligible prime $p$ has $M$ squarefree and $p\equiv1\bmod12$. Whenever $d\mid M$ and $2d-1$ is prime with $1<d<M$, the prime $p$ is absent from A082539. Fixed cutoff tests can discard the finitely many equality cases. For finitely many independent prime coordinates $r\ge5$, the eligible-prime weight for $r\mid M$ is $(r-1)/(r(r-1)-1)>1/r$. Conditioning additionally on the first witness $7p^2+4p+4$ being squarefree keeps the weight at least $1/r$ for $r>7$, since the polynomial at $-1$ is 7.

## Extending fixed small factors

Fix the selected small-prime divisors of $M$ through 73. For a prime $r\equiv5\bmod6$ with $10^9<r\le10^{10}$, the older graph and all older fixed negative-slope tests in that coordinate have ended. If $s$ is the smallest selected prime $5\bmod6$ and $2sr-1$ is prime, $r$ is forbidden. The six included choices $s=5,11,17,23,29,41$ were checked over the full range by two sieves. The remaining small masks keep their previous negative-slope bounds. The input contains these six replayed rows. [Negative-slope data](CunninghamNegativeChecked.jsonl) · [Generator](lagneau_negative_extension.cjs) · [Independent verifier](check_a300984_negative_extension.py)

For $r\equiv1\bmod6$ in the same interval, exclude $2r-1$ prime, already covered by the singleton sieve. Test $2sr-1$ for each selected $s$ in $\{13,43,61,67,73\}$. A signature records which of the five values are prime, so each $r$ is counted once for any selected subset. Two algorithms agreed on all 32 new counts and all 32 outward-rounded block factors. The positive and negative families here use disjoint high-prime coordinates. [Combined positive-slope data](CunninghamPositive10B.json) · [Generator](lagneau_positive_extension.cjs) · [Independent verifier](check_a300984_positive_extension.py)

In a block ending at $u$ with $c$ forbidden primes, the chance of avoiding all of them is at most $(1-1/u)^c\le u/(u+c)$. Each program rounds products upward in integer units of $10^{-15}$. These corrections multiply the earlier estimates within each small-factor choice. The two-selected-small-prime, Janson and singleton estimates from the baseline are retained. [Baseline graph composition](A300984DoubleMasks.md)

## A bound when a medium factor is present

Consider the choices with no selected small prime congruent to $5\bmod6$. Let $t$ range over the 76 primes $73<t\le1000$ with $t\equiv5\bmod6$. If $t$ divides $M$, any prime $r\equiv5\bmod6$ with $14{,}000{,}000<r\le10^9$ and $2tr-1$ prime must be absent from $M$. Each such set of high primes is disjoint from the coordinates on which the earlier graph depends. Every larger vertex of the billion-divisor graph is at most $10^9/74$, and previous singletons and positive-slope tests use $r\equiv1\bmod6$. The existing base divisor sieve through 20 million has no negative one-large-prime test when there is no selected small negative factor. The medium indicators are independent under the base conditions, with activation weights at least $1/t$. The previous graph itself may depend on those medium indicators.

For each center $t$, let $h_t$ be a certified lower bound for having at least one of its high neighbors active. Order the centers so $h_1\ge\cdots\ge h_k\ge h_{k+1}=0$. Suppose the old acceptance event has probability $a\le U$. Let $P_i=\prod_{j=1}^i(1-1/t_j)$. The event that none of the first $i$ centers is active has probability at most $P_i$. Once the medium and all old coordinates are fixed, the high coordinates still have their independent product law. The conditional new failure probability is at least the maximum $h_t$ among active centers. By decomposing that maximum into its ordered level differences, the joint survival probability is therefore at most

$$
a-\sum_{i=1}^k(h_i-h_{i+1})\max(0,a-P_i)
\ \le\ U-\sum_{i=1}^k(h_i-h_{i+1})\max(0,U-P_i).
$$

The final inequality holds because the right-hand function of $a$ is nondecreasing, as the total level width is at most one. This argument allows centers to share high neighbors. Within each cell the implementation similarly multiplies $P_i$ by the cell mass, rounds none-active weights upward and subtracts only losses rounded downward.

The JavaScript and C# programs independently matched all 76 counts and all 76 rounded survival factors. Their counts across centers total 190,060,748, with shared neighbors legitimately counted separately in each center's test. The proof of the displayed inequality handles those overlaps. A finite check also compared the inequality with exact enumeration on 100 small product spaces. [Center data](CunninghamMediumNegative1000.jsonl) · [First sieve](lagneau_medium_negative_stars.cjs) · [Independent C# sieve, select column two equal to zero](CunninghamConditionalStars.cs) · [Inequality implementation](lagneau_star_correction.cjs) · [Exact small tests](check_a300984_star_inequality.py)

## Numerical composition

The normalized numerator before the previous common singleton factor is at most $0.496827904806343$. The existing singleton factor through $10^{10}$ puts it at most $0.486786522775279$. Dividing by the lower bound $0.954333834230937$ for the represented population gives at most $0.510079916811881$. Applying the previously documented census for singleton primes beyond $10^{10}$ reduces this to $0.504840964546$. All these displayed decimal endpoints are rounded outward.

From the directory containing the audit sources and data, the following commands reproduce the composition. The first command builds the existing graph table from its two certificates. The dot argument points to the directory containing those tables.

~~~sh
python lagneau_certificate_union.py Wide1B.json Triple1B.json CertifiedEdgesTriples.json
node lagneau_extended_negative_compose.cjs 20000000 73 . lagneau_negative_1b.json CunninghamNegativeChecked.jsonl CunninghamPositive10B.json CunninghamMediumNegative1000.jsonl
python lagneau_census_composition.py 510079916811881 CunninghamMinus10To100B.txt
~~~

Codex developed and checked these refinements for @dwilfand-sys. This proof uses finite sieve computations and prior analytic bounds. It has no Lean kernel verdict. [Michel Lagneau's A300984](https://oeis.org/A300984)

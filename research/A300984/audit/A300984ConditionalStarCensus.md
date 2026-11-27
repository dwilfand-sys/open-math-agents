# A300984 upper bound with both signs of the medium prime

The limiting share of represented primes in A082539 among distinct represented odd primes of A300984 is at most **0.503580161904**. The majority threshold is 0.5. The result uses the finite high-decade totals of Henri Lifchitz beyond the recomputed range. [Published counts and the wheel inequality](A300984CunninghamCensus.md) · [Previous bounds and graph argument](A300984ExtendedSlopes.md)

## The additional disjoint-coordinate tests

Fix all the small-factor indicators through 73 for $M=(p+1)/2$. Let $s$ be the least selected prime congruent to 5 modulo 6, when present. For every medium prime $t$ with $73<t\le1000$ and $t\equiv5\bmod6$, consider primes $14{,}000{,}000<r\le10^9$ with $r\equiv5\bmod6$ for which $2tr-1$ is prime. When $s$ is present, retain only $r$ with $2sr-1$ composite. This removes the coordinates used by the previous negative-slope test. Exclude any $t$ forbidden by an earlier one-large-prime test in this small-factor choice.

For a medium prime $t\equiv1\bmod6$, require $2t-1$ composite, so $t$ itself survives the singleton test. Use high primes $r\equiv1\bmod6$ in the same interval, with $2tr-1$ prime and $2r-1$ composite. Also require $2ur-1$ composite for every selected $u$ in $\{13,43,61,67,73\}$, which removes all high coordinates already used by the positive-slope test. Exclude any earlier forbidden $t$ as before.

In both cases, concurrent activation of $t$ and a retained $r$ excludes $p$ from A082539 except at a finite number of equalities. As explained in the earlier graph argument, the high coordinates exceed the largest vertex in any earlier nonlinear graph. For $r>14{,}000{,}000$, a prior divisor test through 20 million can use $r$ only without an additional factor, which is already accounted for by the singleton rule. On each sign, apply the ordered-center inequality from the previous note after removing the earlier forbidden coordinates. The second sign uses high coordinates disjoint from the first sign. Thus the prior event in its application may include all the exclusions of the first sign. Independence of high neighbors belonging to different centers is never required.

Two different programs agreed on both the included pair counts and the rounded survival factors for **all 836 negative and 1,312 positive cells**. The negative table has 76 centers and 11 possible choices of least negative small factor, including none. The positive table has 41 centers and all 32 subsets of the five positive small slopes. The C# program inverts the leading coefficient modulo each trial prime to sieve the factor index. The JavaScript verifier instead solves for the complementary factor modulo the leading coefficient, and sums the compatible disjoint signatures directly. [Negative table](CunninghamConditionalStars1000.txt) · [Positive table](CunninghamConditionalPositive1000.txt) · [C# generator](CunninghamConditionalStars.cs) · [JavaScript verifier](check_a300984_conditional_stars.cjs)

The ten negative linear slopes $5,11,17,23,29,41,47,53,59,71$ over the separate interval $(10^9,10^{10}]$ are also included. The Python replay uses the ordinary prime sieve for the factor $r$ and a separate complementary-factor sieve for the shifted value. [Ten-slope table](CunninghamNegative10B.jsonl) · [Python verifier](check_a300984_negative_extension.py)

## The singleton census through 200 billion

The 100 consecutive windows of width $10^9$ in $(10^{11},2\cdot10^{11}]$ contain **194,474,746** prime pairs $r,2r-1$. A second sieve verified every bin. Pair counts in these windows are subtracted from the published total for the full decade before bounding the uncounted remainder. Together with the earlier 900 windows in $(10^{10},10^{11}]$ and the remaining published totals through $10^{15}$, the new reciprocal mass is at least $0.011468471994$. [New census](CunninghamMinus100To200B.txt) · [Independent checker](check_a300984_high_census.cjs) · [Earlier 900 windows](CunninghamMinus10To100B.txt)

The normalized numerator is at most $0.496154646726775$ before the previously computed singleton factor through $10^{10}$, and at most $0.486126871905606$ afterwards. With the represented-population lower bound $0.954333834230937$, the ratio before the extended singleton census is at most $0.509388700755180$. The positive exponential truncation and exact rational rounding used for the sieve give the stated $0.503580161904$ bound.

Run the first command in the previous graph note to build the baseline combined graph. The following two commands reproduce the final composition.

~~~sh
node lagneau_extended_negative_compose.cjs 20000000 73 . lagneau_negative_1b.json CunninghamNegative10B.jsonl CunninghamPositive10B.json CunninghamConditionalStars1000.txt CunninghamConditionalPositive1000.txt
python lagneau_census_composition.py 509388700755180 CunninghamMinus10To100B.txt CunninghamMinus100To200B.txt
~~~

Codex developed the refinement and ran the finite computations for @dwilfand-sys. This bound has no Lean verdict. Four later decade totals use the credit and scope documented in the preceding census note. [Michel Lagneau's A300984](https://oeis.org/A300984)

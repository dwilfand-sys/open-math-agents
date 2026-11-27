# A300984 upper bound when the smaller medium factors are absent

The limiting proportion of distinct represented odd primes of A300984 lying in A082539 is at most **0.502720128266**. This improves the previous bound of 0.503580161904. Both use Henri Lifchitz's published finite prime-pair totals in the higher decades, as documented in the singleton census. [Previous result](A300984ConditionalStarCensus.md) · [Data sources](A300984CunninghamCensus.md)

Fix the base small-prime choice for $M=(p+1)/2$ as in the previous calculation. Let $G$ be the event that no prime in $(73,1000]$ divides $M$. We introduce centers at primes $1000<t\le10000$, with high primes in $4{,}000{,}000<r\le100{,}000{,}000$. The event $t\mid M$, $r\mid M$, $2tr-1$ prime excludes A082539 membership except at one of finitely many equality cases.

The previous singletons and small-slope exclusions are removed by the same tests as before. In particular the relevant least negative slope and the positive-slope mask are retained, and positive center or leaf singletons are excluded. A base divisor test through 20 million cannot combine $r$ with a further admissible factor of at least five. A previous nonlinear divisor through $10^9$ using $r$ would need another prime factor above 73. On $G$, this other factor must exceed 1,000, which makes the divisor exceed $10^9$. All tests from the previous centers at most 1,000 also vanish on $G$. Thus, on $G$, the older graph event is independent of a new high coordinate after fixing everything outside the relevant high coordinates. For the second sign, the first sign's new high coordinates are disjoint.

Let $g$ be a lower bound for the probability of $G$ conditional on the base choice and its individual-prime exclusions. For any still free prime $q\in(73,1000]$, the conditional activation weight is at most $1/(q-1)$ in both of the eligible-prime measures used in the shell calculation. The factor $(q-2)/(q-1)$ can therefore be used in the product for $g$. Coordinates already forced absent contribute one. For a list of centers $t_1,\ldots,t_i$ still free under the base exclusions, the complement of the event that $G$ holds and some listed center is active has probability at most

$$
Q_i=1-g\left(1-\prod_{j=1}^i(1-1/t_j)\right).
$$

The gate primes and the new center primes are disjoint and independent before the graph tests. Order the centers by decreasing certified high-neighbor activation bounds $h_i$, and apply the previous ordered-center inequality with $Q_i$ in place of its none-active bound. The older event can depend on the new high coordinates outside $G$. The lower bound for new failures only counts cases inside $G$, where the requisite independence holds. The implementation rounds $g$ down, none-active weights up, and each subtracted loss down. The ratio uses the same denominator bound as the preceding calculation.

Two programs verified **all 17,894 cells**, including the exact prime-pair counts and each block-rounded factor. There are 530 negative centers with 11 choices of prior negative exclusion and 377 positive centers with 32 positive masks. The tables are gzipped ASCII; each row records center, filter, count and the factor scaled by $10^{15}$. [Negative table](CunninghamLayeredNegative10000.txt.gz) · [Positive table](CunninghamLayeredPositive10000.txt.gz) · [Generator](CunninghamConditionalStars.cs) · [Independent checker](check_a300984_conditional_stars.cjs) · [Exact small examples](check_a300984_star_inequality.py)

The gated centers alone give the upper bound $0.503215684232$. For a separate improvement, in the cells where the least selected negative small prime is five, test $10r-1$ for every prime $r\equiv5\bmod6$ in $(10^{10},10^{11}]$. These high coordinates are disjoint from all the previous negative-slope checks and from all positive singleton pairs. Two algorithms found exactly 240,059,099 pairs in 14,306 blocks and agreed on the rounded survival upper factor $0.993676474711868$. The JavaScript program sieves the two linear forms at their index residues. The C# verifier finds the initial multiple through the congruence of its complementary factor and uses an independent wheel. [New slope row](CunninghamFirstSlope100B.jsonl) · [JavaScript generator](lagneau_negative_extension.cjs) · [C# independent checker](CunninghamLargeLinearReplay.cs)

The normalized numerator is then at most $0.495307294670487$ before the common singleton product through $10^{10}$ and $0.485296645670210$ after it. Dividing by the already proved represented-population lower bound gives at most $0.508518747070613$. Applying the previously verified census through 200 billion and the published high-decade inputs gives $0.502720128266$.

After building the standard combined baseline graph as in the earlier notes, the following commands reproduce the bound and independently verify both added tables.

~~~sh
node lagneau_extended_negative_compose.cjs 20000000 73 . lagneau_negative_1b.json CunninghamNegative10B.jsonl,CunninghamFirstSlope100B.jsonl CunninghamPositive10B.json CunninghamConditionalStars1000.txt CunninghamConditionalPositive1000.txt CunninghamLayeredNegative10000.txt.gz CunninghamLayeredPositive10000.txt.gz
python lagneau_census_composition.py 508518747070613 CunninghamMinus10To100B.txt CunninghamMinus100To200B.txt
node check_a300984_conditional_stars.cjs CunninghamLayeredNegative10000.txt.gz negative 4000000 100000000
node check_a300984_conditional_stars.cjs CunninghamLayeredPositive10000.txt.gz positive 4000000 100000000
~~~

To regenerate the tables with the compiled conditional C# program, use arguments 10000, negative or positive, 1000, 4000000 and 100000000. Run the separate C# large linear verifier with arguments 10000000000, 100000000000 and 5. Codex developed the bound and ran the computations for @dwilfand-sys. The upper bound still exceeds one half. The finite counterexample and the majority conjecture remain open. [Michel Lagneau's A300984](https://oeis.org/A300984)

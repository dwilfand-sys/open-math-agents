# A300984 majority estimate conditional on three published finite counts

Using Henri Lifchitz's published counts of primes $r$ for which $2r-1$ is prime through $10^{13}$, $10^{14}$ and $10^{15}$, the limiting superior of the proportion of represented odd primes in A082539 is **at most 0.499784547217**. It is therefore below one half by at least 0.0215452783 percentage point on those inputs. The proof would refute Michel Lagneau's strict-majority conjecture for all sufficiently large powers of ten. It gives no first failing exponent.

The three finite counts are empirical inputs from [OEIS A401624](https://oeis.org/A401624). They are 15,462,635,138, 132,822,560,771 and 1,153,300,861,300, respectively. We have not independently corroborated them. The [Eindhoven table](https://math.deweger.net/eulerliars/) independently agrees through $10^{12}$. Our complete census also gives 1,604,746,630 pairs in the decade $(10^{11},10^{12}]$, matching the difference of the two published endpoints. This is a conditional computational research result. No Lean kernel check, peer review or historical priority claim is attached.

## Mathematical certificate

For a cutoff $Y$, let $N(Y)$ count distinct odd primes dividing the sequence terms up to $Y$, and $P(Y)$ count those primes in A082539. The [shape argument](A300984DensityAudit.md) reduces the count to eligible primes $p\equiv1\pmod {12}$ with $p+1$ squarefree and $M=(p+1)/2$. A fixed proper divisor $d>1$ of $M$ for which $2d-1$ is prime excludes A082539 membership. The exceptional case $d=M$ affects finitely many $p$ for every finite list of divisors. The representation denominator has a [proved positive lower density](A300984RepresentedLimit.md). The numerator can be bounded by imposing finitely many necessary obstruction tests. This limiting-superior argument suffices without a theorem on the asymptotic distribution of all proper shifted-prime divisors.

For each of 24 small pairs $a,b$ allowed by the earlier graph, select prime leaves $r$ for which $2abr-1$ is prime, subject to the earlier singleton and small-slope exclusion filters. When $a,b,r$ all divide $M$, their product supplies a new forbidden divisor. The [composite-slope proof](A300984CompositeMandatory.md) establishes the permitted intervals, the two separate mandatory factors and the disjoint multiplicative factors. All high-coordinate dependencies are accounted for conditional on the fixed small-prime choice. The independent low-mask check confirmed the older disjoint graph bound is the one actually selected in both eligible-prime measures for each of the 24 indexed masks. The two published center files for each sign contain no center above 50,000. The largest negative center is 49,991 and the largest positive center is 49,999.

Twelve independent replays, one per sign and interval, verified all 39,168 prime counts and each associated block-rounded survival factor. A separate check evaluated the combined inequalities on 128 exact finite product spaces. The rational normalized numerator bound is 0.493075932062700 before the common singleton factor through $10^{10}$, then 0.483110381101760. The denominator lower bound 0.954333834230937 gives **0.506227866783201** before the final finite singleton census. The frozen list consists of 1,330 independently replayed windows, [with cutoffs through 500 billion and a further 30 windows from one trillion to 1.03 trillion](A300984FiftyThousandCenters.md). With the published high totals, the Selberg reciprocal-mass lower bound is 0.012809797542287 rounded down. The simpler wheel-only bound also yields $P(Y)/N(Y)$ limiting superior at most **0.499876159580** on exactly the same inputs.

## Dependence on the upper decade counts

The following upper bounds use the same numerator, independently replayed fine windows and exact Selberg computation. For an omitted boundary the verifier combines adjacent intervals; it never uses the omitted count to recover an interval difference. Fine windows extending beyond the last available boundary still contribute their directly observed reciprocal mass.

| Added published boundary or boundaries above $10^{12}$ | Upper bound |
|---|---:|
| None | 0.501679907553 |
| $10^{13}$ | 0.500953984489 |
| $10^{14}$ | 0.500974585307 |
| $10^{15}$ | 0.501059492432 |
| $10^{13},10^{14}$ | 0.500327968065 |
| $10^{13},10^{15}$ | 0.500342360793 |
| $10^{14},10^{15}$ | 0.500430462149 |
| $10^{13},10^{14},10^{15}$ | **0.499784547217** |

All three high counts are necessary for this particular frozen certificate. Omitting even the directly enumerated 30 windows beyond $10^{12}$ gives a simpler wheel-only upper bound of 0.501713614447 with the frozen independently replayed subset of windows. Substituting our entire primary fine-window computation through $10^{12}$ gives 0.501550426118 on that cutoff. Its decade sum is independently confirmed, while the second per-window replay was incomplete when the certificate was frozen.

The exact published values are stronger assumptions than the proof needs. A separate [one-sided check](check_a300984_cumulative_floor.py) assumes only that the three cumulative counts are at least 13,916,371,624, 119,540,304,693 and 1,037,970,775,170. These are 90% of the reported values rounded down. Reserve the exact frozen window points first, then greedily select additional distinct pairs to meet the successive remaining quotas. Each group uses only its upper endpoint in the rank-packing inequality. The resulting upper bound is **0.499996310180734**. These three floors have not been independently established. The [two-sided tolerance checker](check_a300984_census_tolerance.py) separately gives 0.499907089185018 when the three reported totals are each perturbed independently by up to 5%.

## Reproduction

Build the baseline catalog and prepare the independently replayed center tables as in the [50,000-center certificate](A300984FiftyThousandCenters.md). The [frozen input manifest](A300984Composite24InputHashes.json) includes the uncompressed SHA-256 digest for every composite table. The [C# generator](CunninghamCompositeSlopes.cs) takes sign 1 or 5, lower endpoint and upper endpoint. Compile with a reference to System.Numerics. The replay driver can verify the compressed files, or generate them with the supplied executable and verify the resulting files with the separate JavaScript sieve.

~~~sh
python assemble_a300984_outer_tables.py
python replay_a300984_composite24.py
node check_a300984_low_pair_prior.cjs 20000000 73 .
python check_a300984_composite_mandatory.py
node lagneau_joint_stars_run.cjs 20000000 73 . lagneau_negative_1b.json CunninghamNegative10B.jsonl,CunninghamNegative100B.jsonl CunninghamPositive10B.json CunninghamConditionalStars1000.txt,5@CunninghamMixedNegative5.txt.gz CunninghamConditionalPositive1000.txt,5@CunninghamMixedPositive5.txt.gz CunninghamLayeredNegative10000.txt.gz CunninghamLayeredPositive10000.txt.gz CunninghamMultiple100M1B.txt.gz CunninghamMultiple1B10B.txt.gz CunninghamOuterNegative30000All.txt.gz,CunninghamOuterNegative30000To50000.txt.gz CunninghamOuterPositive30000All.txt.gz,CunninghamOuterPositive30000To50000.txt.gz quantile CunninghamLongNegative250.txt CunninghamLongPositive250.txt A300984CompositeAll.json
python check_a300984_decade_subsets.py 506227866783201 CunninghamMinus10To100B.txt CunninghamMinus100To200B.txt CunninghamMinus200To400B.txt CunninghamMinus400To500B.txt CunninghamMinus1Tto1030B.txt
~~~

To rebuild the composite tables from first principles, pass the compiled generator path to the Python replay driver using its --generator option.

Codex derived the bounds and ran the checks for @dwilfand-sys. Michel Lagneau proposed the conjecture. Henri Lifchitz supplied the three upper decade counts on which the conclusion depends. [OEIS A300984](https://oeis.org/A300984)

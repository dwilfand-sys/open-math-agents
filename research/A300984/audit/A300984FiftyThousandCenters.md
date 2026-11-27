# A300984 with 50,000-center range and Selberg packing

The limiting proportion of represented odd primes in A082539 is at most **0.500516511582**. This improves the [previous bound](A300984ThirtyThousandCenters.md) of 0.500987129998. The upper bound exceeds half by 0.0516511582 percentage point. No first solution or Lean verdict is claimed.

The added centers $30,000<t\le50,000$ use leaves $14,000,000<r\le100,000,000$. Two separate sieves agreed on the count and rounded survival factor of each of the 10,362 added negative-leaf rows and 23,136 added positive-leaf rows. The [replay driver](check_a300984_outer_centers.py) regenerates the thousand-center batches. The [assembly script](assemble_a300984_outer_tables.py) checks their uncompressed SHA-256 digests for each sign and reconstructs both files. The [joint quantile estimate](A300984JointRiskQuantile.md) additionally exploits masks in which the two signs depend on disjoint sets of low primes. The exact finite-product checker passed all 32 twelve-coordinate models at three previous survival bounds.

For each standard center $73<t\le250$, extend its high leaves to the disjoint range $(10^9,3\cdot10^9]$. For positive leaves the new table excludes the singleton $2r-1$ and every small positive slope already selected. For negative leaves use this extension only if at most one negative small prime is selected, and exclude its previous linear obstruction. In those masks the separate table of multiple negative slopes excludes no additional negative leaves. There is no previous nonlinear divisor test with a leaf this large. Given an active center, its two high ranges have independent prime coordinates under either of the eligible-prime measures. The survival upper factors therefore multiply. High leaves for different centers may overlap, as permitted in the [joint-star inequality](A300984JointStarArgument.md). Two implementations agreed on all 176 negative and 288 positive added center/filter rows, comprising 16 and nine centers respectively. [Negative rows](CunninghamLongNegative250.txt) and [positive rows](CunninghamLongPositive250.txt)

The numerator upper bound in the previous normalization is 0.493798071260153 before the common factor through $10^{10}$ and 0.483817925153709 afterwards. The lower bound 0.954333834230937 for the represented-prime denominator gives a ratio at most 0.506969267775779 before the high singleton census.

Beyond the [previous 1,200 individually replayed windows](A300984ThirtyThousandCenters.md), independent programs agreed in each of 100 one-billion-wide windows from 400 to 500 billion and each of 30 one-billion-wide windows from one trillion to 1.03 trillion. The former contain 178,797,659 Cunningham pairs and the latter 50,560,842. [400–500 billion](CunninghamMinus400To500B.txt) and [one trillion to 1.03 trillion](CunninghamMinus1Tto1030B.txt)

The [Selberg packing argument](A300984SelbergPacking.md) strengthens the lower bound on the high reciprocal mass from 0.012626510627749 to 0.012809797542287 (rounded down). Its independent checks evaluated finite sieve identities and directly enumerated the squarefree coefficients at all 16 sieve levels. Applying the rational exponential bound gives the proportion above. This result uses Henri Lifchitz's published totals through $10^{15}$. We independently obtained the full decade total through $10^{12}$, which also matches the Eindhoven group's published count. We have not independently recomputed the totals for $10^{13}$ through $10^{15}$. [Sources](A300984CunninghamCensus.md)

The following arguments follow the existing baseline generation. The comma-separated extended center files are read as one table per sign.

~~~sh
python check_a300984_outer_centers.py negative 50000
python check_a300984_outer_centers.py positive 50000
python assemble_a300984_outer_tables.py
node lagneau_joint_stars_run.cjs 20000000 73 . lagneau_negative_1b.json CunninghamNegative10B.jsonl,CunninghamNegative100B.jsonl CunninghamPositive10B.json CunninghamConditionalStars1000.txt,5@CunninghamMixedNegative5.txt.gz CunninghamConditionalPositive1000.txt,5@CunninghamMixedPositive5.txt.gz CunninghamLayeredNegative10000.txt.gz CunninghamLayeredPositive10000.txt.gz CunninghamMultiple100M1B.txt.gz CunninghamMultiple1B10B.txt.gz CunninghamOuterNegative30000All.txt.gz,CunninghamOuterNegative30000To50000.txt.gz CunninghamOuterPositive30000All.txt.gz,CunninghamOuterPositive30000To50000.txt.gz quantile CunninghamLongNegative250.txt CunninghamLongPositive250.txt
python lagneau_selberg_packing.py 506969267775779 1000,3000,10000,30000,100000,200000,300000,400000,500000,600000,700000,800000,1000000,1200000,1500000,2000000 CunninghamMinus10To100B.txt CunninghamMinus100To200B.txt CunninghamMinus200To400B.txt CunninghamMinus400To500B.txt CunninghamMinus1Tto1030B.txt
~~~

Codex developed and ran the new sieves and bounds for @dwilfand-sys. Michel Lagneau proposed the majority question. [OEIS A300984](https://oeis.org/A300984)

# Two selected small prime factors in the A300984 majority estimate

The limiting upper bound for the proportion of represented primes in A082539 decreases to **0.512283012213088**. This estimate uses the same denominator as the earlier density audit. It does not settle whether the proportion is greater than one half at every finite power of ten.

Condition on the small-factor indicators in the earlier estimate. Write $M=(p+1)/2$, $B=73$, and $C=10^9$. Suppose exactly two of the free small primes, $a$ and $b$, divide $M$ and this small assignment has survived the earlier exclusions. Set $D=\{1,a,b,ab\}$. Use primes $r$ with

$$
B<r\le \min\bigl(\lfloor C/(B+1)\rfloor,\lfloor C/(ab)\rfloor\bigr)
$$

for which every $2dr-1$ with $d\in D$ is composite. This removes the coordinates of every earlier one-large-prime exclusion, including the extended conditional positive and negative slopes and the common singleton exclusions. Primes from the original single-obstruction list already fail when $d=1$. The upper endpoint ensures that the sieve checks every relevant shifted primality against its precomputed primes through $2C$.

Join distinct retained $r,s$ if some $d\in D$ satisfies $drs\le C$ with $2drs-1$ prime. Whenever $r,s\mid M$, this excludes $p$ from A082539 except at the finite equality values $p=2drs-1$. Under the fixed small assignment and earlier linear exclusions, the retained vertex indicators remain independent in density. Their local probabilities lie between $1/r$ and $1/(r-1)$, both for the ordinary eligible measure and the outer first-witness squarefree measure. The earlier test with two outer factors need not be independent. We take the smaller of the old bound and the new Janson bound within each assignment.

The calculation adds the 24 eligible pairs with the smallest products $ab$. The empty and one-selected-prime assignments take the smaller of the older pair and triple Janson bounds. Other assignments retain the earlier estimates. All local bounds are rounded outwards. The combined represented-primitive numerator is at most $0.498883329093667$ before the shared singleton factor and $0.488800404910269$ after it. Dividing by the conservative represented lower bound $0.954160870567672$ and rounding upwards gives the result.

## Reproduction

Run these commands with the scripts and tables in one directory. The independent NumPy replay uses a separate segmented sieve and exactly rechecks all 24 vertex counts, edge counts, integer moments and rational survival factors.

~~~sh
python lagneau_certificate_union.py Wide1B.json Triple1B.json Combined.json
node lagneau_double_mask_graph.cjs 1000000000 73 24 Double1B.json
python lagneau_double_mask_replay.py Double1B.json
node lagneau_compose_masks.cjs 20000000 73 Combined.json Double1B.json Positive1B.json lagneau_negative_1b.json
~~~

The pair and triple input moments can be independently checked with lagneau_wide_replay.py and lagneau_hypergraph_replay.py. The conditional linear tables can be checked with lagneau_extra_one_replay.py and lagneau_negative_replay.py. The common extra singleton factor comes from lagneau_large_singletons_check.py with endpoints 20000000 and 10000000000. The density reduction and analytic tail are in the preceding audit. This is a computationally certified paper estimate, with no Lean kernel verdict.

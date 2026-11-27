# Five small factors of shifted-prime divisors

For a represented odd prime $p$, put $k=(p+1)/2$. This calculation counts obstructions $d=sr$ with $s$ in $\{13,43,61,67,73\}$, $r\equiv1\bmod6$ prime, and $2sr-1$ prime. It uses $r\le10^9$ and excludes every $r$ with $2r-1$ prime. Its factors can therefore multiply the existing large-singleton and $r\equiv5\bmod6$ estimates.

Fix the small primes dividing $k$ in the sieve with maximum divisor $D=20{,}000{,}000$ and small cutoff $B=73$. If at least one of the five primes $s$ was selected, let $m$ be the smallest divisor greater than one of the product of all selected small primes that equals one modulo six. The minimum is the smaller of the least selected prime congruent to one and the product of the two least selected primes congruent to five, omitting nonexistent alternatives. In this model the possible values of $m$ at most 73 are $13,43,55,61,67,73$. The supplied mask calculation also allows the value 55 when that mask is subsequently discarded by a known obstruction.

Restrict to $r>\lfloor D/m\rfloor$. A one-large-prime rule involving $r$ would have form $ar$ with $a$ a selected small divisor, $ar\le D$, and $2ar-1$ prime. Since $r\equiv1\bmod6$, a prime of the last form at these sizes requires $a\equiv1\bmod6$. The only remaining possible $a$ is one, and the calculation excludes $2r-1$ prime. Every two-large-prime rule involving $r$ has another factor exceeding $B\ge m$, so its divisor exceeds $D$ as well. Consequently these $r$ are independent of the earlier obstruction events after fixing the mask, and remain so after conditioning on the relevant small-modulus witness tests.

For a given $r$, several $2sr-1$ may be prime. Record their set as one signature. If this signature intersects the selected small slopes, $r\mid k$ excludes $p$ from A082539, except at one of the finitely many equalities $p=2sr-1$. Recording each $r$ once handles overlaps exactly. Its conditional chance to divide $k$ is at least $1/r$, also in the outermost range where $7p^2+4p+4$ must be squarefree. [Large-prime local probabilities](A300984LargeSingletons.md)

Each block ends at an upper bound $M$ for its primes. Given $c$ newly excluded local choices in the block, the survival probability is at most $M/(M+c)$. The table gives the single-slope values at their respective lower endpoints. Joint masks use the union of their signatures.

| Selected slope $s$ | Additional prime values $r$ | Upper multiplier |
|---:|---:|---:|
| 13 | 2,848,556 | 0.977577212389790 |
| 43 | 2,471,181 | 0.976586024587275 |
| 61 | 2,344,199 | 0.976700655466057 |
| 67 | 2,444,176 | 0.974987156112983 |
| 73 | 2,469,306 | 0.974206392247800 |

The production table stores counts and rounded multipliers for all 192 pairs of a lower threshold and a mask. The JavaScript sieve applies a subset transform to disjoint signatures. The independent Python program uses larger segments and sums the intersecting signatures directly. Its only third-party dependency is NumPy. A second, small-instance Python check uses an ordinary prime table for every integer in range.

~~~sh
node lagneau_extra_residue_one.cjs 20000000 73 1000000000 Positive1B.json
python lagneau_extra_one_replay.py Positive1B.json
node lagneau_extra_residue_one.cjs 10000 73 30000 PositiveSmall.json
python lagneau_extra_one_check.py PositiveSmall.json
~~~

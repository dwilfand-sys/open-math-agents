# A300984 and squarefree witnesses in successive prime ranges

For a bound $X$, set $P=\sqrt X/2$ and count primes relative to the eligible primes up to $P$. Eligibility means $p\equiv1\pmod {12}$ and $p+1$ is squarefree. A witness with prime exponent at least three requires $p\le X^{1/3}$, a negligible proportion. For a witness $2^i p^2$, the squarefree-divisor sum is $3(p+1)$. The other sum is

$$
F_i(p)=(2^{i+1}-1)p^2+(2^{i+1}-4)(p+1).
$$

Only $2\le i\le k$ are possible when $2^{-(k-1)/2}<p/P\le2^{-(k-2)/2}$. Representation in that interval requires at least one of those $F_i(p)$ to be squarefree.

## Conditional residue calculation

For each prime $5\le r\le61$, the obstruction sieve records whether $r\mid (p+1)/2$. Under eligibility, the $r-1$ unit classes modulo $r^2$ with $p\equiv-1\pmod r$ and $p\not\equiv-1\pmod{r^2}$ give the positive case. There are $r(r-2)$ unit classes in the negative case. The prime number theorem in fixed arithmetic progressions and the Chinese remainder theorem give uniform independent local choices after fixing these indicators. Squarefreeness of $p+1$ is obtained by the usual convergent square-divisor sieve.

For each eligible class at $r$, the script records exactly which $F_i$ vanish modulo $r^2$. Fix a set of small divisibility indicators. For any subset of witnesses, the probability that all of them pass every local test is the product of the corresponding class fractions. Inclusion-exclusion gives the probability that at least one witness passes. Multiplying this probability by the shifted-prime sieve weight for the same indicators is valid because the remaining shift tests depend only on divisibility by larger primes. Intersections added in inclusion-exclusion are rounded upward and those subtracted are rounded downward. Every modular test uses integer arithmetic.

## Computed upper bounds

Run `node workSearch/lagneau_band_witnesses.cjs`. The divisor cutoff is $10^7$, the small-prime cutoff is 61, and the shift sieve permits at most one prime factor greater than 61 in each composite obstruction. The $k=2$ band uses the full squarefree-density certificate for $F_2$ from `lagneau_crt_bound.cjs`. All subsequent displayed bounds use finite square tests alone.

| Largest permitted $i$ | Width in $p/P$ | Upper bound on represented primitive primes within the band, relative to eligible primes there |
|---|---|---|
| 2 | $1-1/\sqrt2$ | 0.474282692517819 |
| 3 | $1/\sqrt2-1/2$ | 0.547409181462601 |
| 4 | $(1-1/\sqrt2)/2$ | 0.549872450250246 |
| 5 | $(1/\sqrt2-1/2)/2$ | 0.549933039332124 |
| At least 6 | $1/4$ | 0.549933586916362 |

Weighting these bands gives a normalized numerator at most **0.527244121500252**. Dividing by the independently certified represented proportion of at least **0.954160870567673** gives a limiting upper proportion of **0.552573614957163**. This leaves the strict majority open. The denominator uses the three squarefree witnesses evaluated by `lagneau_rep_density.py` and the finer first-witness product in `lagneau_crt_bound.cjs`.

For the optional two-outer-prime certificate, run `node workSearch/lagneau_band_witnesses.cjs 20000 43 20000 --graph` as a small cross-check. `lagneau_two_outer.cjs` supplies the bound on the remaining large-prime indicators. The conditional square calculation and its rounding are identical.

The larger verified run uses `node workSearch/lagneau_band_witnesses.cjs 20000000 73 20000000 --graph`. The four band bounds in ascending order of exponent are 0.460058236096943, 0.530966183073661, 0.533391303406389 and 0.533453269029138. The inner-tail bound is 0.533453859716221. These give a normalized numerator of at most **0.511432342238356** and a limiting proportion of at most **0.536002217250936**.

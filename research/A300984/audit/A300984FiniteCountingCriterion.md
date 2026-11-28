# A finite counting criterion for the A300984 majority conjecture

The limiting-density argument would refute Michel Lagneau's strict-majority conjecture if every one of 5,621 consecutive intervals of length one billion, from 1.566 trillion to 7.187 trillion, contains at least 1,400,000 primes $r$ with $2r-1$ also prime. This is a sufficient condition. A window below the threshold can still contribute its measured count to the weighted total. The criterion uses the independently corroborated counts through one trillion and the 2,245 archived windows. It requires none of Henri Lifchitz's three larger endpoint totals. [Frozen inputs](https://github.com/dwilfand-sys/open-math-agents/blob/00ba347e6163b7aa6a8a129c801e8ca15fc516f6/research/A300984/audit/A300984PairedEndpoints.md)

## Exact inequality

Let $G=10^{18}$, and let $B=506110650178735/10^{15}$ be the numerator-to-denominator upper bound before the final independent singleton exclusions. The archived calculation supplies 10,014,347,310,684,979 units of reciprocal mass. The least integer $h$ for which $\sum_{j=0}^{5}(h/G)^j/j!>2B$ is 12,147,223,201,673,053. The two sides can be compared with integers. Monotonicity of this polynomial on the positive reals makes this a strict one-half test.

For each disjoint new bin $(L,U]$ with at least $k$ qualifying primes, their reciprocals contribute at least $k/U$. Rounding down separately contributes $\lfloor kG/U\rfloor$ units. These coordinates exceed all frozen ones. Adding 1,400,000 per bin to the archived mass up through 7.186 trillion gives 12,147,051,896,478,830 units. The final bin raises the bound to 12,147,246,692,638,562, which crosses the strict threshold. The earlier conditional sieve supplies the conversion from reciprocal mass to the limiting proportion.

| Minimum count in each billion-integer bin | Number of bins | Sufficient upper endpoint |
| ---: | ---: | ---: |
| 1,300,000 | 6,515 | 8.081 trillion |
| 1,400,000 | 5,621 | 7.187 trillion |
| 1,450,000 | 5,254 | 6.820 trillion |
| 1,500,000 | 4,927 | 6.493 trillion |

The tabulated ranges are verification targets. The archived independent data end at 1.566 trillion. A first implementation counted 702,915,852 pairs in 434 further bins through two trillion. Its smallest bin contained 1,604,347 pairs; using those [additional primary counts](CunninghamPrimary1566To2000B.txt) gives a 50.0869079636% upper bound. The separate implementation is checking those windows. The resulting limiting statement also depends on the mathematical sieve argument. It has no Lean verdict.

Reproduce from the frozen bin file with `python verify_a300984_finite_quota.py CunninghamPairedEndpointBins.txt`. Codex derived the finite criterion for @dwilfand-sys. The conjecture is Michel Lagneau's.

# Frequencies of the first three doublings in A300984

Restrict to the primes $p\equiv1\pmod{12}$ for which $3(p+1)$ is squarefree. For each such prime, record whether $4p^2,8p^2,16p^2$ satisfy the full A300984 condition, in that order. The following percentages enclose the limiting proportions within this restricted set of primes. A single proportion is computed across distinct primes. The three exponent tests are correlated.

| Pattern | Lower bound | Upper bound |
|---|---:|---:|
| 000 | 0.0207652501% | 0.0209152503% |
| 001 | 0.6773632471% | 0.6775132473% |
| 010 | 0.4989757786% | 0.4991257787% |
| 011 | 13.8897860228% | 13.8899360229% |
| 100 | 0.2348916001% | 0.2350416003% |
| 101 | 7.0816983911% | 7.0818483913% |
| 110 | 2.6955814806% | 2.6957314808% |
| 111 | 74.9003382289% | 74.9004882290% |

For each subset of the three exponents, multiply the local proportions at primes up to two million where all its quadratic tests survive. The four quantities at each prime are its eligible unit-class count $r(r-1)-1$ and the three numbers of quadratic roots amongst those classes. The three sets of roots are disjoint for $r\ge5$, since the exponent gaps are 1 or 2; a shared root would give both $x^2+x+1=0$ and $(x+2)^2=0$ modulo $r$. The local roots are checked by trial enumeration through 97 and computed for larger primes using the discriminants and simple-root lifting. Inclusion-exclusion gives the finite-sieve probability of any individual pattern.

For each quadratic, the limiting probability lost at primes beyond an even cutoff $R$ is bounded by the sum of $2/[r(r-2)]$ over all odd integers greater than $R$. The sum telescopes to $1/(R-1)$. The quadratic large-square argument justifies this passage from fixed cutoff to natural prime density. A required 1 in the finite pattern can be lost to the tail. A required 0 in the final pattern can have arisen from a finite 1. Accordingly, subtract the number of 1s times this tail bound from the lower endpoint and add the number of 0s times it to the upper endpoint. Each intermediate product uses outward rounding at precision $10^{-24}$. The final bounds are rounded outwards once more.

Run the checker with python lagneau_three_pattern_density.py 2000000 alongside lagneau_rep_density.py. The program prints lower and upper probabilities in units of $10^{-12}$. These certified intervals concern three doubling tests within eligible primes. They are separate from the A082539 majority statistic.

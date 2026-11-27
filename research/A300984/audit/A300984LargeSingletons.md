# A further finite sieve beyond twenty million

The proportion of distinct represented odd primes in A082539 has limit superior at most **52.842235%**. The finite sample at $10^{38}$ addresses that one cutoff. The analytic upper bound leaves the strict-majority conjecture open.

The two-large-prime calculation and the additional tests on the successive prime ranges use obstruction divisors at most $D=20{,}000{,}000$. Their resulting represented primitive numerator is at most $0.511432342238356$ relative to all eligible primes, and the represented denominator is at least $0.954160870567672$ on that scale. [Two-prime graph](A300984TwoOuter.md) · [Squarefree tests across ranges](LagneauBandWitnesses.md)

For every prime $r>D$ with $2r-1$ prime, the divisibility $r\mid (p+1)/2$ prevents $p$ from belonging to A082539, with the single possible exception $p=2r-1$. A fixed finite list of such exceptions has density zero. These larger-prime divisibility indicators, conditional on eligibility, are independent in density and independent of the smaller-prime tests. The local divisibility probability is $(r-1)/(r(r-1)-1)>1/r$.

The outside-range estimate also conditions on $F(p)=7p^2+4p+4$ being squarefree. At $r>20{,}000{,}000$, none of the local square obstructions for $F$ has $p=-1\bmod r$, since $F(-1)=7$. Removing those local roots reduces the denominator of the conditional divisibility probability while retaining its numerator. Thus $1/r$ remains a valid lower bound on the excluded local probability for every summand used in the four ranges. The fixed-prime CRT distributions and the quadratic square-divisor tail in the initial density proof justify this conditioning. [Density proof](Density.md)

For $20{,}000{,}000<r\le10^9$, the paired sieve finds **3,203,190** primes with $2r-1$ prime. It partitions the candidates $r=6k+1$ into 2,493 consecutive blocks of up to 65,536 values of $k$. A block ending at $M$ with $c$ accepted primes has survival factor at most

$$
(1-1/M)^c\ \le\ \frac{1}{1+c/M}.
$$

The first factor follows by independence. The second bound follows by expanding $(1+1/(M-1))^c$. Multiplying the block bounds with upward rounding gives at most $0.985858509556699$. This common factor bounds the numerator from above, leaving a represented primitive numerator at most $0.504199926658198$. The final limiting upper bound is $0.528422347018095$.

Two implementations independently reproduced both the complete count and the multiplier. The JavaScript program sieves the two linear functions $6k+1$ and $12k+1$ directly. The Python program sieves odd integers in two ordinary intervals by Eratosthenes, then selects the matching entries from the resulting prime tables.

~~~sh
node lagneau_band_witnesses.cjs 20000000 73 20000000 --graph
node lagneau_large_singletons.cjs 20000000 1000000000 511432342238356
python lagneau_large_singletons_check.py 20000000 1000000000
~~~

The Python output is the exact pair count followed by the outward-rounded multiplier in units of $10^{-15}$.

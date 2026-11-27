# Large prime divisors conditional on a small divisor

Write $M=(p+1)/2$ for an eligible prime $p$, let $D=20{,}000{,}000$ be the existing divisor cutoff and let $s\le73$ be the least prime divisor of $M$ congruent to 5 modulo 6. For any prime $r\equiv5\pmod6$ with $D/s<r\le10^9$, primality of $2sr-1$ forbids $r\mid M$ for an A082539 prime, apart from the finite equality cases $p=2sr-1$.

The old finite sieve imposes no condition on such an $r$ after the small divisor indicators are fixed. Indeed, any divisor test involving $r$ has the form $d=rt$, where $d\equiv1\pmod6$. Its remaining factor $t\equiv5\pmod6$ has at least one prime factor congruent to 5 modulo 6. If the test can occur in the specified small-divisor case, that prime is at least $s$, giving $d\ge rs>D$. This argument also covers old tests involving two large primes. The previously computed singleton interval uses only primes congruent to 1 modulo 6, independently of the new interval.

The conditional probability of $r\mid M$ is $(r-1)/(r^2-r-1)>1/r$. The full first-witness squarefree condition can only increase this probability for the primes considered here, because $F_2(-1)=7$. The other witness tests in the band certificate use only small primes. The Chinese remainder theorem therefore permits multiplying the old bound for each small-divisor case by the new independent survival factor.

The program writes $r=6k+5$ and sieves both $6k+5$ and $12sk+10s-1$ by primes up to the square roots of their maximum values. In a block with largest candidate $R$ and $c$ prime pairs, the survival factor is at most $(1-1/R)^c\le R/(R+c)$. All products of bounds are rounded upward.

Run the three-slope computation from the directory containing the scripts.

~~~sh
node lagneau_linear_tail.cjs 20000000 73 20000000 1000000000 5,11,17
~~~

| Least small prime $s$ | Strict lower endpoint for $r$ | Number of prime pairs | Upper survival factor |
|---|---:|---:|---:|
| 5 | 4,000,000 | 4,055,030 | 0.974168003873431 |
| 11 | 1,818,181 | 3,273,697 | 0.976010043290143 |
| 17 | 1,176,470 | 3,086,064 | 0.975965980357017 |

Combining those three slopes with the finite graph and witness bands gives a normalized numerator at most 0.508096907673931. The independent singleton factor lowers this to 0.500911660109790. Dividing by the conservative represented density 0.954160870567672 gives a limiting upper proportion of **0.524976107867195**.

## All ten negative slopes and the positive slope table

The additional least divisors are 23, 29, 41, 47, 53, 59 and 71. All ten pair counts and multipliers are in the saved file `lagneau_negative_1b.json`. An independent Python replay reproduced all ten counts and all ten block-rounded multipliers over their full ranges through one billion. It uses an ordinary sieve for the outer primes and factors each possible composite shifted value to mark the proper index. A dense sieve also matched the counts up to 50,000. The positive-residue sieve tests $r\equiv1\pmod6$ while excluding prime $2r-1$, allowing both the negative slopes and the independent singleton stretch to be applied to the same finite divisor case.

To generate the positive table and replay the joint calculation from the saved negative table, run the following commands in the same directory. Replacing the negative table path with a single dash recomputes every negative-slope entry.

~~~sh
python lagneau_negative_replay.py lagneau_negative_1b.json
node lagneau_extra_residue_one.cjs 20000000 73 1000000000 Positive1B.json
node lagneau_linear_tail.cjs 20000000 73 20000000 1000000000 5,11,17,23,29,41,47,53,59,71 Positive1B.json lagneau_negative_1b.json 1B
~~~

The joint bound before the singleton stretch is 0.505359859008520 on the eligible-prime scale. The table reports results after each choice of singleton cutoff. The final column uses the same lower bound of 0.954160870567672 for the represented proportion. Passing the last argument as `10B` selects the second row.

| Singleton prime cutoff | Upper multiplier | Normalized represented-primitive numerator | Upper limiting primitive proportion among represented primes |
|---:|---:|---:|---:|
| 1,000,000,000 | 0.985858509556699 | 0.498213317391924 | 0.522148133255051 |
| 10,000,000,000 | 0.979789013592184 | 0.495146037767043 | 0.518933497526952 |

Both rows leave the conjectured strict majority open.

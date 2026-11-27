# Auditing the A300984 majority at 10³⁸

Among 3,000 eligible prime draws, at most 1,343 represented primes belonged to A082539 and at least 1,494 represented primes fell outside it. The sample's represented proportion was at most **47.3388%**. The true proportion over all represented primes at this cutoff is still unknown.

Counting follows the finite-set example in the sequence entry. A prime is represented if it divides at least one sequence term at most \(10^m\), regardless of the number of terms it divides. An eligible odd prime satisfies \(p\equiv1\bmod12\), has squarefree \(p+1\), and lies below or at \(\sqrt{10^m}/2\). The source conjecture claims a strict majority among the represented primes for every \(m>7\). [A300984](https://oeis.org/A300984) · [A082539](https://oeis.org/A082539)

## Replay the certificate

From this directory, run these commands with CPython. The reference run used Python 3.13.0 and SymPy 1.14.0. SymPy factors a skipped candidate only when small square divisors leave its eligibility unresolved during the seed replay.

~~~sh
python -m pip install sympy==1.14.0
python lagneau_sample_audit.py A300984Sample.json.gz
~~~

The verifier reconstructs the pseudorandom draws, checks that each accepted prime is eligible, and enumerates every divisor of \((p+1)/2\) to decide A082539 membership. For a primitive prime to be excluded from the upper count, it verifies an obstructing prime square for every possible representative. For each certified nonprimitive representative it verifies the full prime factorization of its nonsquarefree-divisor sum. The deterministic twelve-base Miller–Rabin bound covers integers below \(2^{64}\). For larger prime factors the certificate supplies factorizations of \(q-1\) and Lucas–Pocklington witnesses.

The expected counts are 1,398 eligible primitive draws, 1,343 represented primitive draws as an upper bound, and 1,494 represented nonprimitive draws as a lower bound. Assigning every remaining uncertainty in favor of the conjecture gives \(1343/2837\). Under independent uniform draws with replacement, the one-sided binomial probability for a population proportion of at least 50% is at most **0.002425526245**. For a population proportion of at least 49% it is at most **0.039918426064**. Both displayed probabilities are rounded upward. The test conditions on the number of represented draws. Increasing the primitive count or decreasing the nonprimitive count makes its lower-tail probability larger, which makes the displayed bounds conservative.

## How the sample was selected

An exploratory run tested \(m=21,25,29,35,38\), using 2,400 eligible draws per exponent. Its seeds were \(31415926+m\). Representation in that run was screened for square divisors with prime at most 1,000. The exploratory results motivated the choice \(m=38\). The holdout used a fresh fixed seed, **927413**, and **3,000** draws. Its seed and size were chosen before examining that sample. Python's deterministic generator makes replay possible. Statistical interpretation assumes independent uniform draws and applies to this chosen cutoff. The holdout's three thousand draws include every eligible prime the sampler accepted in sequence.

Factorization ran in two passes on the same draws. The first pass certified 1,393 nonprimitive representatives. The second tried alternative witnesses or longer factorization timeouts for unresolved nonprimitive primes, bringing this count to 1,494. It used the same denominator population, seed, and draws. Both counts certify actual witnesses, and the unresolved cases are accounted for in the conservative bounds. Factorization timeouts depend on the machine, so generating a fresh certificate may recover a different subset of valid witnesses.

With GNU Coreutils `factor` on the command path, these commands reproduce the selection and attempt the same factorizations. The original run used Coreutils 8.32.

~~~sh
python lagneau_prime_sample.py 2400 21 25 29 35 38 --seed 31415926
python lagneau_exact_sample.py 38 3000 927413 --output holdout.json
python lagneau_sample_refine.py holdout.json --seconds 4
python lagneau_sample_audit.py holdout.json
~~~

## Analytic bounds

The independently reviewed one-outer-prime sieve and the three-witness representation estimate give a **55.3131% upper bound** on the limiting upper proportion. Here “one outer prime” describes a fixed obstruction divisor with at most one prime factor greater than 61. This result and the finite sample address different quantities. [Derivation](Density.md)

The numerical certificates run with Node.js and the Python standard library.

~~~sh
node lagneau_crt_bound.cjs
python lagneau_rep_density.py
python combine_bounds.py
~~~

The last command verifies the exact rational combination of the two outward-rounded estimates. The broader project’s Lean checks do not cover this research calculation.

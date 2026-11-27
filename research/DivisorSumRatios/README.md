# The least composite-root examples in two divisor-sum problems

For a positive integer (n), write S for the sum of its squarefree divisors and T for the sum of its other divisors. Michel Lagneau asked in OEIS A301517 if every positive square T/S has prime square root. The related A318807 adds the assumption that S and T are both squares. The first project disproofs, by @anmolspace, use the root 3,107. The smaller root 268 answers both questions and gives the following least inputs.

| Sequence | Least n | S | T |
|---|---:|---:|---:|
| A301517 | 19,773,000 | 1,008 | 72,398,592 |
| A318807 | 4,963,023,000 | 254,016 = 504² | 18,244,445,184 = 135,072² |

The first n factors as 2³ · 3² · 5³ · 13³. The second is 251 times the first. In both rows T = 268² S and 268 = 4 · 67.

## Why the enumeration covers every smaller n

Strip the primes that occur exactly once from n, writing n = c t with c powerful, t squarefree and gcd(c,t) = 1. Both the total divisor sum and S are multiplicative across these coprime factors. Each stripped prime p multiplies both sums by p+1. It therefore also multiplies T by p+1, preserving T/S. It suffices first to find all powerful cores c with a positive square ratio and nonprime root. For A318807, examine the squarefree coprime multipliers up to the desired bound for each such core. Since T/S is a square, the two sums are squares precisely when S is a square.

The first program enumerates the prime exponents of c in increasing prime order. Running `python enumerate_cores.py 25000000000` checks 339,264 cores, including 1, and returns four eligible cores with roots 268, 1292, 3107 and 1682. The second program independently uses the unique form c = a² b³ with b squarefree. For each prime factor of c, exponent parity determines whether it divides b, and the remaining even part determines a. Running `python verify_minima.py` checks 150,557 cores through 4,963,023,000. Exactly three qualify before extension, with roots 268, 1292 and 3107. Exactly one extension in this interval makes both divisor sums squares. These finite minimality checks use ordinary integer arithmetic in Python. The Lean submissions certify the individual numerical counterexamples.

[OEIS A301517](https://oeis.org/A301517) · [Earlier disproof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7662) · [Smaller witness](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10580)

[OEIS A318807](https://oeis.org/A318807) · [Earlier disproof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9203) · [Smaller witness](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10582)

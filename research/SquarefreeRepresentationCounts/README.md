# Exact frequencies of small square-plus-squarefree representation counts

Let R(n) count positive integers k for which n−k² is positive and squarefree. The table in [frequency.csv](frequency.csv) gives, for each j from 0 through 100, the number of positive integers n with R(n)=j and the largest such n. All 101 frequencies and the first 81 last occurrences agree with the explicit conjectural lists in [OEIS A085264](https://oeis.org/A085264). The calculation used the definition of R to generate both columns independently of the published values.

There are exactly two integers with R(n)=0, namely 1 and 13. Exactly nine have R(n)=1: 2, 3, 4, 5, 8, 9, 25, 29 and 61. This answers the question posed in [A085266](https://oeis.org/A085266), which credits Ryan Propper with an earlier search through 625,000,000. The largest integer in any of the 101 levels is 187,425, at level 97. For instance, 867 positive integers have 100 representations, the last being 164,700.

This is a written proof with independently reproduced integer computations. The counting extension has no project Lean kernel verdict. The argument uses the bounds in our [squarefree sieve draft](../../proofs/oeis-a085265.lean), which can also be read at its [fixed revision](https://github.com/dwilfand-sys/open-math-agents/blob/acedc78ebba2903e02b4361c4c7e95e6dafdb367/proofs/oeis-a085265.lean). This note does not establish priority. For the classical asymptotic theory and a related representation theorem allowing the square zero, see Jorge Jiménez Urroz, [Expositiones Mathematicae 40 (2022), 665–678](https://doi.org/10.1016/j.exmath.2021.12.002).

## 1. Candidate squares and the common-prime sieve

Set u=⌊√(n−1)⌋. If 4 divides n, take the odd integers k in [1,u]. Otherwise take the even ones in that interval. Write these J candidates as k=2x+b with 0≤x<J and b equal to 1 or 2, respectively. Each difference is positive and avoids divisibility by 4. Also u≤2J+1.

Let S consist of the odd primes p with p² dividing n, put r=|S|, and write ρ=∏_{p∈S}(1−1/p). Their product is at most √n≤u+1≤2J+2. Remove k sharing a factor with this product. The number left is at least Jρ−e, with e=0 at r=0 and e=2^(r−1) otherwise. Indeed for even k the count of divisibility by each odd d is ⌊J/d⌋, whose discrepancy can be centered at −1/2. For odd k the counts differ from J/d by at most 1/2. Inclusion–exclusion cancels the constant center when r>0, leaving at most 2^r half-unit errors.

For an odd prime p outside S, there are at most two roots of x²=n modulo p². If roots exist, they are opposite nonzero residues. Within a block of p² consecutive integers starting at a multiple of p² these two residues have opposite parity. Thus among the allowed k, hits for p occupy at most ⌊2J/p²⌋+1 positions. Every unsuccessful remaining candidate is hit by an odd prime p≤2J+1 outside S. Subtracting the sum of hit counts gives a lower bound for R(n), since surviving roots k give distinct representations.

## 2. Intermediate range, 1,600≤J≤1,000,000

Write A=S∩{3,5,7,11,13,17} and t=r−|A|. We have (∏A)19^t≤2J+2 and t≤4. For an interval lo≤J≤hi, define c(hi) as the sum of ⌊2hi/p²⌋+1 over odd primes p≤2hi+1. The preceding argument gives
```
R(n) ≥ lo · ∏_{p∈A}(1−1/p) · (18/19)^t
       − c(hi) + ∑_{p∈A}(⌊2hi/p²⌋+1) − e.
```
The aggregate c(hi) minus the displayed refund bounds the increasing cost over primes outside A. Dropping the rest of S from the refund preserves the lower bound. The code enumerates all 64 possible A and all five possible t, retaining only (∏A)19^t≤2hi+2. Its 159 consecutive intervals exhaust the stated range. The smallest certified lower bound is 7731/77>100. It occurs in [1600,1666] at A={5,7,11}, t=0.

## 3. Large range, J≥1,000,000

Write Π(v) for the number of odd primes at most v and C=ρ(29/50 + (2/9)·1_{3∈S}). For 1≤T≤J the refined inclusion–exclusion estimate gives
```
R(n) ≥ J C − Π(2J+1) − 2^r(1+2Π(T)) − J/T.
```
For the derivation see `initial_candidates`, `hit_card_sifted` and `large_hit_total` in the linked sieve. For p≤T, inclusion–exclusion on each of the two possible root classes yields a main contribution at most 2Jρ/p² and an error of at most 2·2^r. For larger p, the raw parity-block estimate applies. The sum of 1/p² over odd primes is at most 21/100, with 1/9 removed when 3 belongs to S. Bounding the sum over odd integers above T by 1/(2T) gives the tail J/T. This deduction bounds the number of surviving squares directly.

For r≤9 use T=128, for which Π(T)=30. The inclusion–exclusion draft proves the following inequalities by prime counting and products of the smallest possible prime factors (lemmas `smallRankCosts`, `smallRankProduct`, `primeCost16` and `primeCost18`).

| r | Lower bound for C | Lower bound for J | Upper bound for Π(2J+1) |
|---|---|---:|---|
| 0 through 6 | 36/125 | 1,000,000 | (J+1)/4+22,000 |
| 7 | 34/125 | 2,400,000 | (J+1)/4+22,000 |
| 8 or 9 | 1/4 | 55,000,000 | (4J+4)/18+262,145 |

Substitution leaves an increasing affine lower bound in each row. At the respective lower endpoints these bounds exceed 4,283, 4,241 and 804,713. For r≥10 take T=16r. The prime-product estimates in `high_budget` give J≥4r·8^r, rC≥87/50, rΠ(2J+1)≤8J/5 and r·2^r(1+2Π(16r))≤J/100. Substituting and multiplying the large-range bound by r gives rR(n)≥(27/400)J. Hence R(n)≥(27/400)·4·8^r>100.

The same estimates prove R(n) tends to infinity. For r≤9 each of the three lower bounds is affine in J with positive slope. For r≥10, the product of the r primes of S is at least 3^r and at most 2J+2, so R(n)≥(27/400)J/log₃(2J+2), which also tends to infinity. Finally J tends to infinity with n. Thus every fixed representation count occurs only finitely often, and each nonempty level has a largest element. This qualitative conclusion also follows from the classical asymptotic estimate for the representation function. Excluding the zero square changes that count by at most one.

## 4. Finite segment and independent verification

For n>3,202²=10,252,804, the candidate count J is at least 1,600. It remains to classify positive n through that bound. The supplied program removes multiples of prime squares to obtain a bitset for positive squarefree integers. Shifting by k² marks exactly the integers represented using root k. Binary addition on bit planes counts representations simultaneously. Through 200,000, the first 512 roots include all possible roots. On the rest of the finite segment those same roots already give at least 101 distinct representations for every integer. The program then reads the entire frequency and last-occurrence table from the fully counted prefix.

A separately implemented scalar check marked multiples of every integer square d² for d≥2. It tried k individually for each n through 10,252,804 and stopped upon finding 101 representations. It reproduced the frequency and last-occurrence arrays. Among n>200,000 the largest root ever needed to find the 101st representation was 503, attained at n=5,336,100. The intermediate intervals and large-range constants were also re-evaluated independently with integer or rational arithmetic.

Run `python count_squarefree_representations.py` with Python 3.10 or newer. The program uses only the standard library. The independent scalar implementation runs with `node check_squarefree_counts_independent.cjs`. The related OEIS sequence defining R(n) is [A085263](https://oeis.org/A085263).

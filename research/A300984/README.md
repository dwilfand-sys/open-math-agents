# The divisor-sum conjectures for A300984

For n>0 let S be the sum of the squarefree positive divisors, and T the sum of the other divisors. Michel Lagneau's OEIS entry considers the n for which S and T are both squarefree. It states two conjectures, which are recorded separately in the project statement.

## Forced shape

S is the product of 1+p over the distinct prime factors p of n. If n had two distinct odd prime factors, then 4 would divide S. Also, for each prime q, there must be a different prime p with p² dividing n. Otherwise each nonsquarefree divisor would be divisible by q², and hence so would T. This includes T=0. Together these observations imply n = 2^i p^j with i,j ≥ 2. The squarefreeness of S = 3(p+1) excludes p=3, p≡3 mod 4 and p≡2 mod 3. Thus p≡1 mod 12. The standalone Lean proof also shows that 676 is the least member by checking its divisor sums 42 and 1,239. On 27 November 2026 the Lean 4.37.0-rc1 web editor checked the conjectured shape, the strengthened exponents and congruence, and the exact minimum. Each axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`. The project’s pinned checker has not issued an upstream verdict for A300984. [Standalone Lean proof](LagneauPrimeShape.lean)

## A correction at ten million

The prime 937 is absent from the published list E. The integer 3,511,876 = 2² · 937² has nine divisors. Its two divisor sums are 2,814 = 2·3·7·67 and 6,149,535 = 3·5·7·58,567, both squarefree. Also 13+1 divides 937+1, so 937 does not belong to A082539. With the missing prime included, 39 of 47 represented primes belong to A082539 at this bound.

## Exact finite counts

For each admissible odd prime p through the square root of B/4, the programs search all exponent pairs with i,j≥2 and 2^i p^j≤B. They compute total divisor sums through finite geometric series and retain each represented prime once. The Python implementation uses integer factorization. The independent C# implementation removes prime factors singly up to the cube root of the remaining integer and checks whether the remainder is a square. Its final obstruction test enumerates divisors d of (p+1)/2 to look for a smaller prime of the form 2d−1.

| m | Represented primes up to 10^m | In A082539 |
|---:|---:|---:|
| 7 | 47 | 39 |
| 8 | 132 | 98 |
| 9 | 382 | 269 |
| 10 | 1,084 | 750 |
| 11 | 3,087 | 2,053 |
| 12 | 8,880 | 5,670 |
| 13 | 25,639 | 15,783 |
| 14 | 74,802 | 44,947 |
| 15 | 218,702 | 128,324 |
| 16 | 644,008 | 369,981 |
| 17 | 1,903,971 | 1,072,924 |

The counts through m=12 agree across the two implementations. The original full divisor-sum test also recovers all 46 terms up to 500,000 without using the shape theorem. The data through m=17 satisfy the strict majority. The assertion at every higher exponent remains open in this investigation.

On Windows, load the C# file with `Add-Type -Path (Resolve-Path LagneauMajority.cs)` then run `[LagneauMajority]::Run(17)`. Alternatively run `python lagneau_majority.py 12` (requires SymPy), or `python check_lagneau_shape.py 500000` (standard library).

[OEIS A300984](https://oeis.org/A300984) · [OEIS A082539](https://oeis.org/A082539) · [Formal statement](https://github.com/dwilfand-sys/open-math-agents/commit/bb1877d0c1babf6efa1904052bc05eed72daf0c4) · [Reduction](https://github.com/dwilfand-sys/open-math-agents/commit/324a0fd2a35df3a01c3445a6804b4c627ef796fb)

# Sums of powerful numbers through one billion

Among the positive integers through 1,000,000,000, exactly six cannot be written as a sum of at most three powerful numbers. They are 7, 15, 23, 87, 111 and 119. An integer is powerful if every prime that divides it also has its square dividing it. The integer 1 is powerful. Zero below denotes an unused summand.

The computation proves a stronger finite statement. Exactly 20 integers in the same range lack a representation as a powerful number (possibly zero) plus two nonnegative squares. In increasing order these are

**7, 15, 23, 39, 55, 71, 87, 103, 111, 119, 167, 335, 559, 783, 895, 951, 1455, 1551, 2127, 5655.**

Mollin and Walsh conjectured the unrestricted six-exception result. Heath-Brown proved that the exception set is finite. OEIS credits Paul Jobling with checking below 40,000,000 in 2001. This computation has 25 times that stated upper bound. The computations and this note were developed by Codex for @dwilfand-sys. This is a reproducible finite computation. The upper limit is part of the result, and historical priority has not been established. [OEIS A056828](https://oeis.org/A056828)

## The residue class that needs computation

Legendre's three-square theorem supplies a representation by three nonnegative squares for every positive integer except those of the form `4^a(8k+7)`. A nonzero square is powerful, so one of the squares can serve as the powerful term. Multiplying a representation `c+x²+y²` by 4 gives `4c+(2x)²+(2y)²`. If c is powerful, then 4c is powerful, since multiplication by a square preserves the condition on prime exponents.

It therefore suffices to test the 125,000,000 positive integers congruent to 7 modulo 8 up to the bound, then examine square multiples of the exceptions. For such an integer n, a representation `n=c+x²+y²` must use an odd c that is 3, 5 or 7 modulo 8. An even powerful number is divisible by 4 and squares modulo 8 are 0, 1 and 4. For each admissible c the difference is 0, 2 or 4 modulo 8. Searching powerful c up to 200,000 was sufficient to cover every candidate except the 20 listed. Each of those 20 is at most 5,655, so the search covers every possible nonnegative c for them. Only 70 distinct offsets added coverage when tested in increasing order. The last was 171,125.

## Two independent computations

Run the two scripts with Python and NumPy.

```sh
python check_mollin_walsh_packed.py 1000000000
python check_mollin_walsh_fermat.py 1000000000
```

The first program enumerates all pairs of nonnegative square roots x ≤ y with x²+y² ≤ the bound. Stepping through y in the appropriate classes modulo 4 limits the work to one residue r at a time. Its Boolean table has one entry per k for the possible values 8k+r. For r=0, 2 and 4, respectively, the counts are 22,922,236, 43,260,782 and 22,027,007 for 0 ≤ k < 125,000,000. Zero is included in the first count. The NumPy square and index arithmetic uses signed 64-bit integers and all squared sums enumerated here are at most one billion. The temporary Boolean tables are packed into bitsets. Direct trial division checks whether an offset is powerful.

The second program builds the same three tables without enumerating pairs of squares. By Fermat’s two-square theorem, a positive integer is a sum of two squares precisely when each of its prime factors congruent to 3 modulo 4 has even valuation. For m=4j+1 ≤ 499,999,997, only such primes up to the square root of this limit need testing. If a larger prime had odd valuation, the congruence m≡1 modulo 4 would force a different prime of this type with odd valuation, and both could not exceed the square root. For each tested prime p, the program marks multiples of p, removes multiples of p², marks multiples of p³, and so on. The accumulated defects fit in an unsigned byte. Their number at any point is at most one plus the number of distinct prime factors, which is less than 31 since m < 2³⁰.

Powers of 2 do not affect two-square representability. Thus 8k+2 uses the entry for 4k+1, and 8k+4 uses the entry for 2k+1 whenever that odd part is 1 modulo 4. For 8k with k>0, write k as a power of 2 times its odd part. The program separately marks zero. It obtains the same class counts. This implementation generates powerful offsets as a²b³. Every integer of this form is powerful, and every positive powerful integer has this form by splitting each prime exponent ≥2 as twice a nonnegative integer plus three times a nonnegative integer.

Both programs shift the bitset for residue 7−(c mod 8) by floor(c/8) to mark candidates reached by each c. Python integers hold the packed bits exactly. They obtain the same ordered residual set. They also exhaust possible summands directly in the residual range.

## From the primitive residuals to all integers

The table gives a powerful c and nonnegative square roots with 4e=c+x²+y². It follows by square scaling that 4ᵃe is represented for every a ≥ 1. The final column gives three powerful summands for each residual where they exist. At the six remaining values exhaustive summation supplies the negative check.

| e | c | x | y | Powerful summands for e |
|---:|---:|---:|---:|---|
| 7 | 8 | 2 | 4 | none |
| 15 | 8 | 4 | 6 | none |
| 23 | 27 | 1 | 8 | none |
| 39 | 8 | 2 | 12 | 4 + 8 + 27 |
| 55 | 8 | 4 | 14 | 1 + 27 + 27 |
| 71 | 27 | 1 | 16 | 8 + 27 + 36 |
| 87 | 8 | 4 | 18 | none |
| 103 | 8 | 2 | 20 | 4 + 27 + 72 |
| 111 | 8 | 6 | 20 | none |
| 119 | 8 | 12 | 18 | none |
| 167 | 27 | 4 | 25 | 27 + 32 + 108 |
| 335 | 8 | 6 | 36 | 27 + 108 + 200 |
| 559 | 8 | 28 | 38 | 216 + 343 |
| 783 | 72 | 12 | 54 | 108 + 675 |
| 895 | 72 | 12 | 58 | 4 + 243 + 648 |
| 951 | 8 | 14 | 60 | 32 + 343 + 576 |
| 1455 | 8 | 6 | 76 | 4 + 128 + 1323 |
| 1551 | 8 | 36 | 70 | 4 + 216 + 1331 |
| 2127 | 8 | 6 | 92 | 4 + 800 + 1323 |
| 5655 | 8 | 36 | 146 | 4 + 243 + 5408 |

## Why the finite set of offsets cannot cover all primes

Let C be any finite set of positive powerful offsets. For each c in C, choose a different odd prime q_c ≡ 3 modulo 4 with q_c not dividing c. Require n ≡ c+q_c modulo q_c² and n ≡ 7 modulo 8. The Chinese remainder theorem gives a residue class relatively prime to its modulus. By Dirichlet’s theorem it contains infinitely many primes n larger than all the offsets. For each c, q_c then divides n−c exactly once. Fermat’s two-square theorem excludes n−c from the sums of two squares. The offset c=0 can also be allowed because n≡7 modulo 8 already excludes two squares. A global proof using a powerful offset and two squares would thus require the choice of positive offsets to grow beyond any fixed finite set, even when the candidate integers are restricted to primes.

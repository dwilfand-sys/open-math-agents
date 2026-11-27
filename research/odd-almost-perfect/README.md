# Odd almost-perfect numbers

This checkpoint studies the odd case of Hiphex’s reduction of A215926. The Lean reduction proves that an odd integer with odd divisor sum is a square. The companion proof excludes odd squares greater than one with at most three distinct prime factors. Both Lean files passed the project’s static checker. Kernel verification is pending.

For an odd square with four or five distinct prime divisors, the certificate lists a finite binary partition of all possible primes and exponents. The primes are ordered, and all exponents are positive even integers. At a prime split, one branch fixes the smallest remaining prime at its lower bound. The other branch advances that lower bound to the next prime. At an exponent split, one branch fixes an exponent at its even lower bound and the other raises it by two.

For a prime power, its divisor ratio is the finite sum of reciprocal powers of the prime. This ratio increases with the exponent and is bounded by the prime divided by its predecessor. Multiplying these bounds gives a lower ratio, an upper ratio, and a lower bound for the integer. Each leaf verifies that the lower ratio is at least two or that the upper ratio plus the reciprocal of the lower integer bound is strictly less than two. Both comparisons exclude an almost-perfect number.

| Distinct primes | Certificate nodes | Ratio at least two | Upper ratio excludes equality |
| --- | ---: | ---: | ---: |
| 4 | 571 | 148 | 138 |
| 5 | 315,407 | 104,255 | 53,449 |

Run these commands from this directory with Python 3. The generator uses a geometric quotient and trial division. The independent replay uses direct sums of reciprocal powers, a sieve of primes, and integer cross-multiplication.

```sh
python generate.py 4 5
python replay.py 4 5
python verify_three.py
```

`FourPrimeExclusion.lean` contains the four-prime argument as an explicit Lean theorem. It checks all 286 exclusions using rational arithmetic and splits using prime gaps and even exponents. Run `python render_cases.py` to regenerate its case splits and `python audit_four.py` to compare the tests, branches and boxes in the Lean source with the replayed certificate. The Lean file awaits a kernel run.

The four- and five-prime certificates have been replayed in Python. They are independent computational proofs of known results. Kishore excluded odd almost-perfect numbers with five prime factors in 1978. [Mathematics of Computation](https://doi.org/10.1090/S0025-5718-1978-0485658-X)

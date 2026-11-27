# Exhaustive search for the first additional A279821 member

The native sieve examines every integer in each indicated closed interval. It checks the full prime-radical congruence first, then independently evaluates the necessary prime-power congruences for every surviving composite. Prime squares are outside A279821 by definition.

| Closed interval | Squarefree survivors | Survivors with a repeated prime | Actual members |
|---|---:|---:|---:|
| 2…30,000,000 | 6 | 386 | 11 |
| 30,000,001…200,000,000 | 0 | 144 | 0 |
| 200,000,001…650,000,000 | 0 | 131 | 0 |

Consequently every member up to 650,000,000 is one of Sun’s eleven listed numbers. Across the three segments, 667 composites survived the prime-radical filter, including six squarefree members. The other 661 passed to exact prime-power testing. The twelfth term exists and lies strictly above 650,000,000 and at or below 1,316,632,279. This census stops at 650,000,000.

## Why the sieve covers the full interval

For each prime p up to the square root of the upper endpoint U, the sieve walks the multiples of p in consecutive blocks. It divides out every power of p, records repeated factors, and tests each surviving integer n using the full base-p digit product for T(n) modulo p. It precomputes the integers T(d) modulo p for d<p by the recurrence d T(d)=(2d−1)T(d−1)+3(d−1)T(d−2), whose division by d is valid in this range. Any remaining factor q>1 is prime and exceeds the square root of U. In that case n=qm with m<q, so T(n) modulo q is just T(m) modulo q. The sieve uses the exact integer value of T(m) for this last test. It removes primes and squares of primes. Thus it retains exactly the eligible integers passing every distinct prime test. The Chinese remainder theorem settles every squarefree survivor immediately.

For a repeated factor pᵃ, [the separate checker](check_survivors.py) computes T(n) modulo pᵃ via a direct finite multinomial sum or by expanding the identity P(x)ᵖ=P(xᵖ)+pG(x), with P=x⁻¹+1+x. Terms of degree at least a in pG vanish modulo pᵃ. The remaining finitely many terms recurse at smaller indices. It also uses the proven central-trinomial adjacent congruence of Pan and Sun to reduce an index when p≥5 and its valuation permits that reduction at the working precision. The checker factors every candidate independently, reconstructs its residue modulo n by CRT, and prints a certificate in JSON lines.

A separate calculation using the exact, unreduced integers T(n) at every n through 50,000 recovered all 99 radical survivors and all seven members in that interval. Full self-tests of the prime-power implementation checked 1,525 individual coefficients and included positive and negative controls.

## The stronger congruence modulo n²

The same all-integer census verifies Sun's separate conjecture T(n)≠1 modulo n² for every composite n≤650,000,000. Every composite outside the prime squares and the eleven A279821 members already fails modulo n. The [additional checker](check_a002426_n2.py) gives a prime-power obstruction for each of the eleven members and tests the missing prime squares. For p≥5 it uses Pan and Sun’s bound T(p²)≡T(p) modulo p⁴ and the explicit first digit of (T(p)−1)/p². The primes 2 and 3 are checked directly. The checker verified every one of the 4,435 prime squares up to 1,800,000,000; all 4,433 harmonic residues at p≥5 were nonzero. An independent modular-inverse recurrence reproduced all those harmonic residues. This larger limit pertains to prime squares alone; the complete all-composite check stops at 650,000,000. The [output](square-modulus-controls.jsonl) includes exact local obstructions for the recorded members and a reproducible digest of the prime-square table. Sun's [A002426 entry](https://oeis.org/A002426) reports an earlier all-integer check through 800,000.

## Reproduction

Compile [A279821Sieve.cs](A279821Sieve.cs) with the .NET Framework compiler and the System.Numerics reference. Following the same commands using a compatible modern .NET installation is also possible.

~~~text
csc /nologo /optimize+ /r:System.Numerics.dll /out:A279821Sieve.exe A279821Sieve.cs
A279821Sieve.exe 2 30000000 candidates-2-30000000.txt
A279821Sieve.exe 30000001 200000000 candidates-30000001-200000000.txt
A279821Sieve.exe 200000001 650000000 candidates-200000001-650000000.txt
python check_survivors.py candidates-2-30000000.txt
python check_survivors.py candidates-30000001-200000000.txt
python check_survivors.py candidates-200000001-650000000.txt
python check_sieve_prefix.py candidates-2-30000000.txt 50000
python check_a002426_n2.py --limit 1800000000 --prime-table prime-square-controls.csv
~~~

The archived tabulations use the labels squarefree and repeated. The raw independently produced first and second certificate streams had SHA-256 values eb9b7a0c46eab57aac458a068de0baf05dab8ca2ada2f435f5687362e6ee38a7 and a3eaafe7297c85345aa25d4ab17413306386875ad43103435c1fcd2a7408a2fe, respectively. For the third segment the corresponding digest is 32e6d9186685f698d2719b7d43c2f93966e32be7fa728737a954159e96c479e1. Newline encodings affect file digests.

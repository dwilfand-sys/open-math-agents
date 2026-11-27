# Exhaustive search for the first additional A279821 member

The native sieve examines every integer in each indicated closed interval. It checks the full prime-radical congruence first, then independently evaluates the necessary prime-power congruences for every surviving composite. Prime squares are outside A279821 by definition.

| Closed interval | Squarefree survivors | Survivors with a repeated prime | Actual members |
|---|---:|---:|---:|
| 2…30,000,000 | 6 | 386 | 11 |
| 30,000,001…200,000,000 | 0 | 144 | 0 |

Consequently every member up to 200,000,000 is one of Sun’s eleven listed numbers. The separately proved witnesses give an upper bound of 1,316,632,279 for the twelfth term. This interval is subject to further narrowing as the search proceeds.

## Why the sieve covers the full interval

For each prime p up to the square root of the upper endpoint U, the sieve walks the multiples of p in consecutive blocks. It divides out every power of p, records repeated factors, and tests each surviving integer n using the full base-p digit product for T(n) modulo p. It precomputes the integers T(d) modulo p for d<p by the recurrence d T(d)=(2d−1)T(d−1)+3(d−1)T(d−2), whose division by d is valid in this range. Any remaining factor q>1 is prime and exceeds the square root of U. In that case n=qm with m<q, so T(n) modulo q is just T(m) modulo q. The sieve uses the exact integer value of T(m) for this last test. It removes primes and squares of primes. Thus it retains exactly the eligible integers passing every distinct prime test. The Chinese remainder theorem settles every squarefree survivor immediately.

For a repeated factor pᵃ, [the separate checker](check_survivors.py) computes T(n) modulo pᵃ via a direct finite multinomial sum or by expanding the identity P(x)ᵖ=P(xᵖ)+pG(x), with P=x⁻¹+1+x. Terms of degree at least a in pG vanish modulo pᵃ. The remaining finitely many terms recurse at smaller indices. It also uses the proven central-trinomial adjacent congruence of Pan and Sun to reduce an index when p≥5 and its valuation permits that reduction at the working precision. The checker factors every candidate independently, reconstructs its residue modulo n by CRT, and prints a certificate in JSON lines.

A separate calculation using the exact, unreduced integers T(n) at every n through 50,000 recovered all 99 radical survivors and all seven members in that interval. Full self-tests of the prime-power implementation checked 1,525 individual coefficients and included positive and negative controls.

## Reproduction

Compile [A279821Sieve.cs](A279821Sieve.cs) with the .NET Framework compiler and the System.Numerics reference. Following the same commands using a compatible modern .NET installation is also possible.

~~~text
csc /nologo /optimize+ /r:System.Numerics.dll /out:A279821Sieve.exe A279821Sieve.cs
A279821Sieve.exe 2 30000000 candidates-2-30000000.txt
A279821Sieve.exe 30000001 200000000 candidates-30000001-200000000.txt
python check_survivors.py candidates-2-30000000.txt
python check_survivors.py candidates-30000001-200000000.txt
python check_sieve_prefix.py candidates-2-30000000.txt 50000
~~~

The archived tabulations use the labels squarefree and repeated. The raw independently produced first and second certificate streams had SHA-256 values eb9b7a0c46eab57aac458a068de0baf05dab8ca2ada2f435f5687362e6ee38a7 and a3eaafe7297c85345aa25d4ab17413306386875ad43103435c1fcd2a7408a2fe, respectively. Newline encodings affect file digests.

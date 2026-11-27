# Six-prime certificate for odd almost-perfect numbers

The finite partition rules out an odd almost-perfect square with exactly six distinct prime divisors. Both the generator and the independent verifier exhaust 820,939 nodes. Together with the smaller certificates, this gives the computational bound of at least seven distinct prime divisors for any odd almost-perfect number greater than one. The full conjecture remains open.

| Distinct primes | Prefix-tree nodes | Gzip bytes |
| --- | ---: | ---: |
| 4 | 59 | 92 |
| 5 | 1,173 | 1,079 |
| 6 | 820,939 | 668,093 |

The generator encloses each ordered prime and each positive even exponent in an interval. The verifier rebuilds the partition from explicit prime or exponent cutoffs. It uses rational fractions, computes finite divisor ratios by summing powers, checks prime bounds by trial division for small primes and uses odd-number bounds thereafter. Each child covers one side of its parent’s cutoff. The program rejects a run that leaves any uncovered branch.

For an almost-perfect factorization with a coprime core `B` and an odd prime power `p^e`, put `D = 2B - σ(B)` and `G = 1+p+…+p^(e−1)`. Substituting the geometric identity gives `(2B−Dp)G = D−1`. The deficiency is positive, and `D=1` would force `p=2B`. Thus `Dp < 2B < D(p+1)`. This bounds the possible prime in every coordinate using the divisor ratio of the other factors.

For an odd square `n=r²`, every prime `q` dividing `σ(n)=2r²−1` makes two a quadratic residue modulo `q`, so `q ≡ 1,7 (mod 8)`. Every geometric factor of the divisor sum must therefore also be one or seven modulo eight. For a prime congruent to one, three, five or seven modulo eight, the corresponding allowed even exponents modulo eight are respectively `{0,6}`, `{0,4}`, `{0,2}` and `{0,2,4,6}`. Further elementary modular checks apply because every prime divisor of `n` sees its divisor sum as minus one, and the divisor sum of an almost-perfect odd square is one modulo sixteen.

From this directory, verify the existing files, or regenerate them and verify again. The six-prime replay can take several minutes.

```sh
python replay_six.py 4 5 6
python emit_six.py 4 5 6
python replay_six.py 4 5 6
python check_extension.py
```

A separate exact search additionally checks divisibility by primes up to 3,000 in the forbidden residue classes. It excludes the six-prime case in 277,987 nodes. Run it with the following command.

```sh
python -c "from modular_boxes import prove; print(prove(6, 600, extension=True, sieve=True))"
```

The Lean source files contain the core-extension theorem, the prime-factor sieve, and the modular obstructions. Kernel verification of these files and of an end-to-end six-prime proof remains pending.

Kishore excluded odd almost-perfect numbers with five distinct prime factors. Shnoudi’s October 2026 report gives a computational lower bound of eight and distinguishes computational results from the formally checked lemmas. The present six-prime trace independently reproduces a weaker bound. The inequalities and the first six-prime traversal were developed before locating that report. The stronger local-factor sieve is also described by Shnoudi. [Kishore, Mathematics of Computation](https://doi.org/10.1090/S0025-5718-1978-0485658-X) · [Shnoudi’s project](https://lifeofresearch.com/articles/144) · [Reported research archive](https://doi.org/10.5281/zenodo.23674490)

# Kummer congruences for relations of real cyclotomic units

Given a signed p-th power relation among the real cyclotomic generators, reduce each integer exponent modulo p and absorb the removed p-th powers into the unit. Map the relation to F_p[T]/(T^(p−1)) by ζ ↦ 1+T. Frobenius kills nilpotents, and reversing each geometric sum gives a polynomial congruence. The geometric-series logarithmic derivative and the Bernoulli generating identity give the Bernoulli-weighted vanishing of all its even moments. Restoring the original exponents leaves those residues unchanged.

The target is Hanan Beer's reduction #7897, following the work of Riccardo Brasca and the KummerCriterion contributors. The sign identity comes from Hanan Beer's #7356. The local Bernoulli-moment argument implements the strategy in @Iraeeee's #7722, based on Vandiver's geometric-factor method.

The Lean kernel has not been run on this checkpoint. The project static gate accepts the exact import, declaration, target and file size. Run `python3 check_moments.py` for an independent truncated-polynomial check over all primes through 67. At the irregular primes 37, 59 and 67 it enumerates all 163 satisfying exponent vectors. For nonzero generators it also checks reversed geometric sums, unit Frobenius, and signed exponent normalization.

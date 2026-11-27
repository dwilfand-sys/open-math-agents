# Real cyclotomic units and the ramified residue ring

Assume that a prime p divides the class number of the maximal real subfield of the p-th cyclotomic field. The squared real cyclotomic units generate a subgroup of index 2^((p−3)/2) times that class number. An element of order p in the quotient yields a p-th power relation with at least one exponent nonzero modulo p. Normalizing its integer exponents preserves the unit relation, including its sign.

The integral cyclotomic power basis gives a homomorphism to A = F_p[T]/(T^(p−1)) carrying ζ to 1+T. Every unit's p-th power in A is a nonzero scalar. The two conjugate geometric sums for each real cyclotomic generator multiply to (1+T)^(−a−1) times the square of its forward sum. Multiplying through by the appropriate power of 1+T proves the polynomial divisibility required in reduction #7722.

The class-number index comes from Hanan Beer's accepted PR #7878, which integrates Riccardo Brasca's KummerCriterion and flt-regular. The quotient-group and torsion arguments are from Hanan Beer's reduction #7356, following @Noctluxis. The statement and local congruence route are from @Iraeeee's #7722. The proof preserves the original contributors and Apache-2.0 source references.

The Lean kernel has not been run on this checkpoint. The project static gate accepts the exact import, declaration, target and file size. Run `python3 check_moments.py` for an independent truncated-polynomial check over all primes through 67. At the irregular primes 37, 59 and 67 it enumerates all 163 satisfying exponent vectors. For nonzero generators it also checks reversed geometric sums, unit Frobenius, and signed exponent normalization.

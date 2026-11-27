# Finite relaxations of Carter’s scales case

For the canonical graph `0x3da1087`, the exact-cover problem has 44,483 candidate exterior points and 2,280 equations. The attached data verifies feasibility over the nonnegative rationals and over the field with two elements. Existence of an integral exact cover remains unresolved by these tests.

| Calculation | Result |
|---|---:|
| Graph automorphisms | 16 |
| Orbits of cover equations | 184 |
| Distinct candidate signatures on those orbits | 2,883 |
| Positive representatives in the rational witness | 105 |
| Total rational weight | 95 |
| Rank of the full incidence matrix over GF(2) | 1,361 |
| Candidates in the binary witness | 905 |

Run the verifier from this directory. It uses Python's standard library and the accompanying `weight16_exact_cover.py`.

```sh
python verify_case4_relaxations.py --rank
```

`Case4Relaxations.json` identifies a point by its sorted incident A indices and its sorted matching of B indices. For each rational representative, the verifier applies every graph automorphism and adds the specified integer numerator to every equation the transformed point covers. The required total for each equation is 16 times the stored denominator `5899081338405611347988`. The verifier also checks that each transformed matching covers precisely the remaining support indices once.

The binary witness lists the selected candidates explicitly. Each of the 2,280 equations must receive an odd number of incidences. The optional `--rank` calculation enumerates all candidates and performs Gaussian elimination on the full matrix over GF(2). Neither witness needs an optimization solver or floating-point arithmetic for verification.

# Three sparse weight-16 configurations

The canonical words at indices 1, 2 and 3 in `weight16_exact_cover.py` cannot extend to the 80-row incidence matrix in the sparse weight-16 reduction of Erdős 723. This is a finite computer enumeration. A formal derivation from the project's Lean matrix hypotheses remains open.

| Index | Canonical word | Fixed pairs of four-secants | Compatible starts | Seed orbits | Interiors at orbit representatives | Interiors at all labeled starts | Available hidden points per interior |
|---:|---|---|---:|---:|---:|---:|---:|
| 1 | `0x2e69807` | 45, 46, 56 | 64 | 6 | 258 | 2,272 | 5–26 |
| 2 | `0x3569807` | 01, 45 | 96 | 24 | 2,367 | 9,700 | 5–42 |
| 3 | `0x35a5807` | 24, 35, 47, 56 | 256 | 76 | 219 | 644 | 7–27 |

Here 45 denotes the unique intersection of four-secants 4 and 5, with labels starting at zero. A start chooses the two-secants through each of those specified intersections. The automorphism group preserving the set of specified pairs acts on the compatible starts. The search chooses one representative per orbit. The table's labeled counts sum the number of interiors per representative multiplied by its orbit size.

An interior gives all 44 exterior points incident to at least one four-secant. Its eight local blocks have been checked for all shared line-pair constraints. A full configuration must have 51 additional exterior points on no four-secant. Each stored interior gives two two-secants that miss on the original support and on all 44 points. The direct verifier enumerates every hidden matching containing that pair and finds a repeated intersection with the 44 known points every time.

## Reproduction

Run from this directory. The search and its independent verifier use the Python standard library. The raw JSON files and the compressed word-2 records use the same integer block indices; `sparse_records.py` verifies compression by an exact round trip. 

```sh
python other_sparse_cases.py --case 1 --output Case1SparseSearch.json
python other_sparse_cases.py --case 2 --lazy --output Case2SparseSearch.json
python other_sparse_cases.py --case 3 --output Case3SparseSearch.json
python verify_sparse_records.py 1 Case1SparseSearch.json
python verify_sparse_records.py 2 Case2SparseRecords.json
python verify_sparse_records.py 3 Case3SparseSearch.json
python verify_sparse_enumeration.py 1 Case1SparseSearch.json
```

The last command re-enumerates all eight blocks by conditioning on two colours at a time, using compatibility indexed directly by the 80 incident lines. For word 1 it recovers all 258 stored interiors. `--compact` renumbers the domains separately at each seed, preserving the original indices in the output.

Carter introduced the weight-16 starting configurations. Lam, Thiel and Swiercz used computational searches on these configurations, and Bright and coauthors published SAT certificates. The current Lean project's incidence reduction and graph indexing are due to @avivorly. [Background and starting cases](https://uwaterloo.ca/mathcheck/w16) · [Bright et al., IJCAI 2020](https://www.ijcai.org/proceedings/2020/203) · [Sparse reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3941) · [Scales child](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4185)

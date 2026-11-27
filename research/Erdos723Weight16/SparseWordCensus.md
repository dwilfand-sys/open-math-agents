# The six sparse weight-16 starting configurations

All six cubic graph words in the sparse 80-row reduction of Erdős 723 fail the required line intersections. This is an exhaustive computational result for eight four-secants and 72 two-secants in a hypothetical plane of order ten. A full Lean proof of the project statement remains open.

| Index | Graph word | Interiors at chosen seed representatives | Interiors with fixed graph labels | Full graph-group orbits | Missing-pair certificates |
|---:|---|---:|---:|---:|---|
| 0 | `0x1da9807` | 1,645 | 6,696 | 149 | [Cube](https://github.com/dwilfand-sys/open-math-agents/blob/af8f10c7a37eda6dec613eb79c90c1250001d6f6/research/Erdos723Weight16/CubeExclusion.md) |
| 1 | `0x2e69807` | 258 | 2,272 | 190 | [Three sparse words](OtherSparseWords.md) |
| 2 | `0x3569807` | 2,367 | 9,700 | 622 | [Three sparse words](OtherSparseWords.md) |
| 3 | `0x35a5807` | 219 | 644 | 163 | [Three sparse words](OtherSparseWords.md) |
| 4 | `0x3da1087` | 4 | 16 | 1 | [Scales](ScalesExclusion.md) |
| 5 | `0xfc02187` | 48,338 | 623,784 | 611 | [Explicit records](Case5SparseRecords.json) |

Graph labels distinguish the eight four-secants and their induced 72 two-secants. The four private exterior points of each four-secant are unordered. The six graph words represent 643,112 interiors with graph labels fixed, forming 1,736 orbits. Each interior exhibits a pair of two-secants with no common point on the support, among the 44 specified exterior points, or among any permissible hidden exterior points.

## Two disjoint complete graphs on four vertices

The graph at index 5 consists of the complete graphs on vertices 0–3 and 4–7. Its 16 support points form a 4-by-4 grid. There are 21,408 choices for the entire exterior block on each four-secant. A second enumerator, using an exact cover of its 36 missing two-secants and three shared intersection labels, recovered all 171,264 local blocks.

Fix the double-point types 01, 23, 45 and 67. The four matchings must have mutually compatible intersections. There are 6,272 ordered starts and 131 orbits under the graph automorphisms preserving this set of four types. The search covers every start by choosing one representative per orbit. Each compatible eight-block assignment specifies 44 exterior points.

The 48,338 resulting interiors permit between 6 and 70 individual hidden matchings each. Exactly 54 interiors allow at least 51 candidates. Every interior still exhibits a pair of two-secants that no candidate can join. The largest seed alone contributes 17,408 interiors. The archive contains each assignment's eight local block numbers, number of hidden opportunities, and one such missing pair. Its seventeen data parts and manifest total 687,888 bytes. The manifest provides a SHA-256 digest for each part.

The independent verifier checked 23,197,596 possible hidden meetings across the 48,338 records. Comparing all raw native assignment lists with the archive gave exact agreement across all 131 starts up to symmetry. The graph has 1,152 automorphisms. Its 611 full-group interior orbits comprise one of size 24, four of size 96, three of size 144, nine of size 288, nine of size 384, 99 of size 576 and 486 of size 1,152.

## Reproduction

Run these checks in this directory. The literal verifier constructs the 44 points for each stored interior, verifies the A-line constraints and enumerates every possible hidden matching through the recorded pair.

```sh
python verify_sparse_records.py 5 Case5SparseRecords.json
python sparse_record_census.py 5 Case5SparseRecords.json
python sparse_stabilizers.py 5 Case5SparseRecords.json
python scales_audit_blocks.py --case 5 --domains-only
```

A native enumeration reconstructs the complete set of interior assignments directly from the point and block data. The example uses a C# compiler on Windows and an empty output directory.

```powershell
python word0_native_input.py word5-input.bin --case 5
csc /nologo /optimize+ /out:cube-search.exe word0_search.cs
mkdir native-word5
.\cube-search.exe word5-input.bin 0 131 native-word5
python sparse_record_census.py 5 Case5SparseRecords.json --native-dir native-word5
```

A separate Python traversal reconstructs compatibility from the 80-row incidence relation. Its `--compact` option restricts and renumbers each seed domain. The output keeps the original block indices.

```sh
python other_sparse_cases.py --case 5 --compact --output Word5PythonSearch.json
```

The project reduction and graph numbering are due to @avivorly. Carter introduced the weight-16 starting configurations. Lam, Thiel and Swiercz investigated them computationally, and Bright and coauthors published SAT certificates. [Project reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3941) · [Scales and other-five split](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4185) · [Historical cases](https://uwaterloo.ca/mathcheck/w16) · [Bright et al., IJCAI 2020](https://www.ijcai.org/proceedings/2020/203)

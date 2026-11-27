# No sparse completion of Carter's cube

The graph word `0x1da9807` admits no matrix satisfying the sparse 80-row, weight-16 incidence conditions. This is a computational verification in the project's labels. Carter, Lam, Thiel and Swiercz studied weight-16 codewords, and Bright and coauthors subsequently certified Carter's cube case by SAT. The calculation below uses a different exact-cover formulation. A Lean kernel proof connecting this search to the project theorem is outstanding. [Original project reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4185) · [MathCheck cube case](https://uwaterloo.ca/mathcheck/w16) · [Bright et al.](https://www.ijcai.org/proceedings/2020/203)

## Finite search

The 16 support points are the nonedges of the cubic graph. The 72 two-secants (B-lines) correspond to pairs of support points with disjoint graph endpoints. An exterior point on A-lines indexed by $J$ selects a perfect matching of the support points missed by $J$. There are 12 points with two A-lines, 32 with one A-line, and 51 with no A-line. The construction and counting are given in [ExactCover.md](ExactCover.md).

Each A-line has exactly 12,920 possible blocks of three double points and four single points. Independent exact cover on the individual points regenerated all eight block lists. Every solution must choose one point of type $(0,1)$ and one of type $(4,5)$. Each has ten possibilities. Of the 100 ordered choices, 96 are compatible. The eight cube automorphisms preserving the unordered pair of types partition these 96 choices into 25 orbits.

Fix each representative in turn. Choose one block on each A-line, requiring the two incident blocks to agree on every shared double point. Distinct points must not repeat any unordered pair of A- or B-lines. The search enumerated 1,645 complete block tuples across the 25 representatives. Restoring the orbit sizes of the initial choices gives 6,696 distinct labelled inside configurations.

Each of the 1,645 tuples has two B-lines which have yet to meet and cannot meet at a hidden point. A hidden point would have to contain both lines in a perfect matching on the support. After deleting their four endpoints, all possible matchings of the remaining twelve support points were enumerated. Every matching repeats a B-line pair which already met at an inside point. This prevents extension for that tuple. Relabelling gives the same conclusion across its entire initial orbit.

Independent group enumeration reconstructed all 6,696 labelled configurations from the representatives and divided them into 149 full cube orbits. Of those, 132 have trivial stabilizer, 11 have stabilizer order two and six have stabilizer order three. Direct symmetric searches independently recover the 11 and six exceptional orbits. [Symmetry calculation](CubeSymmetry.md)

## Reproduction

The files accompanying this note include all 1,645 eight-block tuples and a specific missing pair for each. The TSV columns are the zero-based seed, the block index on each A-line, and the two B-line indices. The summary gives the orbit multiplicity and a SHA-256 digest of the sorted tuples and missing pairs for each seed. The whole TSV's SHA-256 with LF line endings is `6f4ed76fefefd253e938caf35b4cf5c6783e95fda5b355e796824a6b598f0857`. [Terminal certificates](CubeInsideCertificates.tsv) · [Per-seed summary](CubeUnrestrictedSummary.json)

Starting in this directory, create an empty output directory named `run`. Supply the native traversal with tables derived from the original sparse word, then verify its outputs:

```sh
python word0_native_input.py run/cube.bin
csc -nologo -optimize+ -platform:x64 -out:run/cube-search.exe word0_search.cs
run/cube-search.exe run/cube.bin 0 25 run
python word0_check_rows.py run --output run/summary.json --witnesses run/certificates.tsv
python word0_group_count.py run/summary.json run/certificates.tsv
```

The traversal uses primitive integer row-pair resources. All tuple and obstruction checks are ordinary Python integer computations. In the verifier each recorded inside tuple must cover all 12 double types and 288 missing A–B incidences exactly once. Every B–B incidence is checked for multiplicity, and each missing pair is tested again by enumerating just the matchings containing that pair.

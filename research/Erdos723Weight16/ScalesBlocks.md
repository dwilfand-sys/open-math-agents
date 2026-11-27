# Two starting cases for Carter’s scales graph

The graph word is `0x3da1087`, in the ordering of the upstream weight-16 reductions. The indices below use the lexicographic support-edge and B-line order in `weight16_exact_cover.py`.

All 16 automorphisms fix B6 and B35 individually. These two B-lines have no common support point, so they meet at a unique exterior point. Enumerating perfect matchings gives 459 candidates for that point. The 16 automorphisms give 52 orbits, including 48 with no incident A-line, three with one A-line and one with two A-lines.

## Two forced incidences

At the exterior intersection of A1 and A2, delete the eight support edges touching vertex 1 or 2. Of those remaining, the support edge `(0,7)` is disjoint only from `(3,4)`. Its required partner in the matching is therefore `(3,4)`. That pair is B35. At the intersection of A5 and A6, the same argument works in reverse. The support edge `(3,4)` is disjoint only from `(0,7)` among the remaining edges.

B35 misses exactly A1, A2, A5 and A6 on the support. Its two forced double points account for all four intersections. Its other seven exterior points lie on no A-line. B6 can pass through at most one of the two double points, since it meets B35 only once.

Each of the two forced double points has three possible matchings. One of their nine joint choices shares B6 as well as B35 and is impossible. The eight remaining choices fall into two orbits of size four.

| Representative | B-lines at A1∩A2 | B-lines at A5∩A6 | Possible B6∩B35 points for this representative |
|---|---|---|---:|
| B6 passes through A1∩A2 | 6, 17, 26, 35 | 0, 35, 41, 61 | 1 |
| B6 misses both double points | 7, 17, 25, 35 | 0, 35, 41, 61 | 320 |

Taking group images of the surviving intersections removes 49 of the 459 candidates. The 410 survivors occupy 45 of the 52 original orbits. This excludes every singleton-A orbit and four of the 48 empty-A orbits. Pairwise consistency of full A blocks leaves all 45 of these orbits represented. The complete search for both starts is recorded in [ScalesExclusion.md](ScalesExclusion.md).

In either case B35 has 55 B-line partners outside the support. Six meet it at the two double points. The remaining 49 B-lines are edges of a 7-regular graph on the 14 support indices outside B35. Its seven hidden points must partition these edges into seven perfect matchings. Other B-pair intersection constraints continue to apply across those matchings.

## Reproduction

The scripts use Python's standard library. `inside_blocks.py` enumerates the three double-point and four singleton-point matchings on each A-line, treating the latter four as an unordered partition. The exact numbers of complete blocks in line order are `4960, 1848, 1848, 4960, 4960, 1848, 1848, 4960`. `search_blocks.py` uses compound blocks in the one-anchor relaxation. A node or time limit yields `UNKNOWN`.

```sh
python inside_blocks.py
python scales_forced_doubles.py
python scales_fixed_intersection.py
python scales_block_consistency.py
python search_blocks.py --case 4 --anchor 35 --nodes 10000 --seconds 10
```

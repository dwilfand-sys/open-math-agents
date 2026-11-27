# Symmetry of the cube starting case

Any completion of the sparse 80-row incidence conditions for the word `0x1da9807` would have a 44-point inside configuration with trivial stabilizer in the automorphism group of its starting graph. The statement concerns the 12 exterior points on two four-secants and the 32 exterior points on one four-secant. A symmetry of this partial configuration is excluded even when the other 51 exterior points could break it.

The starting graph is a cube. Its complementary graph on the eight four-secants comprises two copies of $K_4$ joined by a matching of four opposite vertex pairs. Its 16 edges are the support points. Accordingly the automorphism group is $S_4\times C_2$, of order 48. This is Carter's case II. Prior searches excluded all full planes in this case. The finite result here concerns which inside configurations can extend under the sparse incidence equations. [Carter and MathCheck starting cases](https://uwaterloo.ca/mathcheck/w16) · [Bright et al., IJCAI 2020](https://www.ijcai.org/proceedings/2020/203) · [Original sparse reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4185)

## Exhaustive inside counts

A nontrivial subgroup of the group of order 48 contains an element of order two or three. Conjugate permutations give equivalent searches. The tuple lists the images of the eight zero-based vertex labels. Each row counts individually labelled inside configurations invariant under that particular permutation.

| Order | Class size | Permutation | Inside configurations | Passing the missing-pair test |
|---:|---:|---|---:|---:|
| 2 | 1 | 4,5,6,7,0,1,2,3 | 0 | 0 |
| 2 | 3 | 1,0,7,6,5,4,3,2 | 88 | 0 |
| 2 | 3 | 5,4,3,2,1,0,7,6 | 0 | 0 |
| 2 | 6 | 0,1,3,2,4,5,7,6 | 0 | 0 |
| 2 | 6 | 1,0,6,7,5,4,2,3 | 0 | 0 |
| 3 | 8 | 0,2,3,1,4,6,7,5 | 24 | 0 |

An A block chooses its three double points and four singleton points. An invariant block choice propagates around its orbit of A-lines. A repeated occurrence of the same shared double point denotes one point. Two *different* points sharing two lines contradict the incidence axioms. The search retains exactly the block tuples satisfying these compatibility tests.

For each surviving tuple, there is a pair of B-lines that does not meet in the support or at a chosen inside point. Every possible hidden point is a perfect matching on the 16 support points. The search checks all matchings that contain the missing pair. Every one of these repeats a pair of B-lines already together at an inside point. No symmetry assumption enters this last check.

The independent checker searches orbits of individual points directly. It requires the 12 double-point types and 288 missing A–B intersections to be covered exactly once. It allows each of the 1,980 disjoint B-line pairs to be covered at most once. A candidate orbit that covers a constraint twice is discarded. Selecting whole candidate orbits then exhausts the invariant inside configurations. Once a tuple is found, this checker fixes two prescribed B-lines and enumerates matchings on their remaining 12 support points independently.

Run `python word0_orbit_blocks.py 1` and `python word0_verify_symmetry.py 1` for the second row. Replace the index with 0 through 5 for the other representatives.

## A short proof for the central involution

The central involution exchanges the two $K_4$ parts. It fixes the four support points from the joining matching and pairs the remaining twelve support points. A B-line joins two disjoint edges of the support graph. Exactly 12 B-lines are invariant. Six join pairs of the four fixed support points. The other six join a support point to its mate in the opposite $K_4$.

Suppose the involution preserved the entire sparse completion. An invariant exterior point cannot be on just one A-line, because all A-lines move. Nor can its two A-lines form a double point, because opposite A-lines meet at a support point. Thus every invariant exterior point is hidden. Its matching pairs the four fixed support points amongst themselves. There are three possible pairings. Each gives two B-lines, whose intersection is unique, so at most three exterior points can be invariant.

There are 30 transposed pairs of B-lines. The lines of each pair meet once, at a fixed point. At each fixed support point, three of the nine incident B-lines are fixed, leaving three transposed pairs. Each invariant exterior point has eight incident B-lines, of which at least two are fixed, so it contributes at most three further transposed pairs. The total is at most $4\cdot3+3\cdot3=21$, contradicting 30. This argument applies to the full sparse configuration. The stronger assertion for its inside portion follows from the exhaustive counts above.

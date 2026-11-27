# An exact-cover formulation of the sparse weight-16 cases

This is a reduction of the sparse 80-row subproblem in Erdős 723 to a finite exact-cover search. No infeasibility certificate is asserted here. The six graphs and the original incidences come from Carter's weight-16 starting cases and the existing project reductions, in particular [#2728](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2728), [#3941](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3941) and [#4185](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4185).

Let the eight vertices be the four-secants, denoted by A. Fix the cubic graph G on them that records the exterior intersections of pairs of four-secants. The 16 nonedges of G are the points in the code support S. A two-secant (a B-line) is an unordered pair of members of S with no common A endpoint. There are 72. Each member of S lies on nine B-lines.

Take J to be empty, a singleton A, or a graph edge of G. A candidate exterior point is (J,M), where M is a perfect matching of the S-points whose endpoint sets avoid J, using B-lines as the matching edges. M therefore has 8, 6, or 4 edges respectively. Matching edges are disjoint as pairs of S-points. Their underlying A endpoints may overlap.

Select candidates to cover each of the following exactly once.

| Constraint | Count | Candidates covering it |
|---|---:|---|
| Graph edge J | 12 | Candidates having this double J |
| A pair (b,a) with the B-line b missing the four-secant a on S | 288 | b belongs to M and a to J |
| Unordered pair of B-lines that share no S-point | 1,980 | Both B-lines belong to M |

An incidence matrix gives such a cover. Through each exterior point the lines joining it to the sixteen support points meet them exactly once, as in #3941. Its four-secants account for four support points each and each two-secant accounts for two. This gives M. Uniqueness of the intersection of two lines supplies each exact-cover constraint.

Conversely, each chosen candidate specifies all lines incident with an exterior point. The exact-cover constraints ensure that every two distinct lines meet once when combined with their already prescribed intersections on S. Hence distinct columns share at most one line. For a fixed A row, 36 B-lines miss it on S. Its three double-J columns cover twelve of these, so exactly four singleton-J columns must cover the remaining 24, six at a time. For a fixed B-line b, exactly 55 other B-lines share no support point with it. If t exterior points contain b, the sum of the sizes of J over those points is four, since b misses exactly four A-rows. Counting its 55 partners gives 55 = 7t − 2·4, so t = 9. Counting B incidences over all exterior points gives 72·9 = 12·4 + 32·6 + 8z, with z = 51 empty-J points. This reconstructs exactly 111 columns, all row sizes, and the required incidences of the sparse statement.

The candidate counts in upstream word order are 45,017, 44,765, 44,903, 44,661, 44,483 and 44,301. Each is checked by exact enumeration in `weight16_exact_cover.py`. There are 2,280 exact-cover constraints in every case.

`search_inside.py` implements a smaller necessary condition. It keeps all candidates with nonempty J and only empty-J candidates incident with a chosen B-line. Coverage of graph edges, missing A–B pairs, and disjoint B pairs involving the chosen line is exact. Other disjoint B pairs may be covered at most once. A search stopped at its time or node limit reports UNKNOWN. Bright and coauthors solved related Boolean encodings using the inside columns and five further columns on a common two-secant. Their independently produced certificates concern their encoding. [Paper](https://www.ijcai.org/proceedings/2020/203) · [Starting cases and certificates](https://uwaterloo.ca/mathcheck/w16)


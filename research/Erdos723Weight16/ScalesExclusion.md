# Computer search for the sparse scales configuration

The canonical word `0x3da1087` admits no matrix satisfying the sparse 80-row, weight-16 incidence conditions in `H1` of [open-math-agents PR 4185](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4185). This result comes from an exhaustive Python calculation. A Lean proof connecting it to the project statement is pending.

## Scope and prior work

The calculation uses eight four-secants, 72 two-secants, and the requirement that an exterior point is on at most two four-secants. It addresses one of six graph words in the project’s sparse reduction. Carter introduced the starting cases in his 1974 work. Lam, Thiel and Swiercz searched weight-16 configurations in 1986. Bright, Cheung, Stevens, Kotsireas and Ganesh later published SAT certificates for the weight-16 cases. The graph normalization and two-secant indexing in the project are due to @avivorly. [MathCheck starting cases](https://uwaterloo.ca/mathcheck/w16) · [IJCAI 2020 paper](https://www.ijcai.org/proceedings/2020/203) · [PR 2728](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2728) · [PR 3941](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3941)

## Incidence conditions used

The 16 support points are the nonedges of the labeled cubic graph on A. Each B-line joins two support points with disjoint A endpoint sets. A nonhidden exterior point specifies its nonempty set of incident A-lines and a perfect matching on all support points those A-lines miss. Actual exterior points satisfy these conditions because every support point and every other point have exactly one common line. Every pair of distinct lines meets exactly once. Therefore distinct exterior points share at most one line.

An A block comprises all three shared double points on that A-line and its four private single points. Their B-line sets partition the 36 B-lines missing A on the support. Two adjacent A blocks must agree on their shared double point. Otherwise a pair of blocks can coexist only if no pair of lines lies on two different points. These necessary conditions follow directly from the original incidence matrix. Two forced B35 incidences reduce the possible starts to the two orbits in [ScalesBlocks.md](ScalesBlocks.md).

## Exhaustive results

| Canonical start | Compatible A1 blocks | Four low blocks admitting a candidate at each high row | Complete eight-block choices | Extendible through B35 |
|---|---:|---:|---:|---:|
| B6 belongs to the A1/A2 point | 648 | 18,854 | 4 | 0 |
| B6 misses both distinguished double points | 600 | 9,260 | 0 | 0 |

The four complete choices form one orbit under the order-four stabilizer of the first start. Each gives 44 nonhidden exterior points. The seven remaining exterior points on B35 have no A incidence. Combining every allowed hidden matching through B35 with the already specified points leaves exactly eight candidate hidden matchings. Twelve of the 49 B-lines requiring an intersection at such a point occur in none of them. For the first record in [Case4InsideConfigurations.json](Case4InsideConfigurations.json), B1 is one such missing partner. B1 and B35 also have no common support point and do not intersect at an already specified exterior point.

## Reproduction

Run these commands from this directory with Python. The scripts use the standard library. The first independently enumerates the local block domains by direct exact cover and compares all 629,515,008 directed compatibility entries with literal row-pair incidences. The next two traverse the eight-colour clique problem in different orders. The last verifies the stored 44-point records and the missing partners directly.

```sh
python scales_audit_blocks.py
python scales_complete_blocks.py --output Case4InsideConfigurations.json
python scales_independent_search.py
python verify_scales_inside.py
```

The independent minimum-domain search visits 226,745 states in the first start and 167,798 in the second. It returns the same four block tuples. Both searches traverse finite domains without a time or node cutoff.

`Case4SplitCertificate.json` records a branching colour at each of the 394,539 nonterminal states. The replay checker chooses every possible member of the recorded colour and independently tests all remaining domains. The certificate cannot suppress a branch. It is 197,412 bytes and can be replayed without running the search that generated it.

```sh
python scales_split_certificate.py
```

`ScalesTerminal.lean` contains a separate theorem for each of the four recorded matrices. Its general lemma proves that an incident-line predicate covering all 16 support pencils would pass a finite compatibility search. The four concrete checks exclude the indicated missing B35 partner. The Lean source has been audited against the pinned list APIs and independently simulated, with 89–103 recursive search states per check. Compilation and the project-level bridge from the original matrix hypotheses are pending.

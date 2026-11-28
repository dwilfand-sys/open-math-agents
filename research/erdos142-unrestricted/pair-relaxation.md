# A second-level relaxation for the 117-point obstruction

28 November 2026, Codex for @dwilfand-sys. Computational research only.
No new exact extremal value, formal proof, or publication-priority claim.

Let x_i indicate a selected integer in [1,N], with sum x_i=K. Introduce
symmetric formal variables y_ij, intended to be x_i*x_j, with y_ii=x_i.
Every actual set satisfies

- 0 <= y_ij <= x_i and y_ij <= x_j;
- x_i+x_j-y_ij <= 1;
- sum_j y_ij = K*x_i.

For each arithmetic window W with known maximum c=r5(|W|), it also satisfies

    sum_(i in W) y_ij <= c*x_j,
    sum_(i in W) (x_i-y_ij) <= c*(1-x_j).

These follow by multiplying sum_(i in W) x_i<=c by x_j and 1-x_j.
They apply to every j, including j inside W. Together they form a necessary
second-level Boolean moment relaxation. This is a standard optimization
construction applied here, not a new general mathematical theorem.

The implementation starts from all ordinary AP-window caps and the
pair-product consistency equations. It separates up to 2,000 violated
multiplied-window inequalities per iteration. It imposes no configuration
shape, residue-profile restriction, or other worker's computational result.
The base caps come from OEIS A003004 through 115 and r5(116)<=68.

A feasible intermediate LP only satisfies the inequalities added so far.
Only a converged separation run would establish numerical feasibility of
the full relaxation. Neither one would construct a real 69-point set.
Numerical infeasibility is also insufficient: reconstruct an exact rational
dual or another replayable certificate before asserting a new upper bound.

The first-level obstruction is now proved with explicit rational feasible
weights and independent exact Python/C++ audits; see
Erdos142-fractional-obstruction.md. It is no longer based only on the
floating-point optima. The second-level experiment below is separate.

Controls: N=24,K=18 is numerically infeasible already at the initial LP;
N=25,K=18 is the known feasible positive control. See the corresponding
JSON files for the completed separation result and the main N=117 run.
All times and iterations are recorded separately from proof claims.

The 25-point positive control converged after 42 LP solves (iteration 41),
with maximum remaining numerical violation below 1e-12. This checks the
separation loop on a feasible case; it is not a new bound. The 117-point
run has a 420-second total cap, including its LP solver time limits.

Main 117 result: UNKNOWN after 420.124 s. The last
LP hit its time limit. Intermediate feasible points still violated omitted
cuts; neither full feasibility nor infeasibility was established.

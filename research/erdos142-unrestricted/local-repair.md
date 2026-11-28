# Local repair exclusion for the 118-point near miss

28 November 2026. Source construction: @Draconna, desk note #200424.
New search/replay: Codex for @dwilfand-sys. No first-discovery, kernel-check,
or unrestricted extremal-value claim.

The source mask (bit x denotes integer x) is
632625408446542538220931436864347870.
It selects 70 integers in [1,118] and contains precisely one five-term AP,
{10,35,60,85,110}. Deleting 118 gives a 69-point near miss in [1,117]
with the same sole forbidden AP. Removing 10 as well gives valid lower
witnesses of sizes 69 in 118 and 68 in 117, useful as direct positive controls.
These lower bounds were already known.

A radius-r repair deletes at most r original points and inserts the same
number of previously absent points. No table upper bounds, forced-endpoint
conditions, reflection restriction or other worker's exclusions are imposed.

For both near misses, MiniCard and an independently constructed CP-SAT
model reject every repair through radius 4. The solver-free replay also
enumerates every removal set of sizes 1 through 4 and every possible legal
insertion. Removal sets missing the sole original AP are immediately rejected.
For every other removal set, candidates are inserted in increasing order;
an insertion is legal exactly when it completes none of the four-point
remainders of a five-term AP. If fewer candidates remain than required,
the branch closes. Adding points cannot undo a forbidden AP, so this
pruning loses no solution. The JSON files contain the complete counts.

Thus a valid repair of the 118-point near miss needs at least five deleted
and five inserted points. This is a local statement, not an exclusion of
all 70-point sets in [1,118]. The same four-replacement exclusion holds for
the 117-point truncation.

At radius 5, both bounded solvers were UNKNOWN for N=118. For N=117,
CP-SAT returned INFEASIBLE, while the independently configured MiniCard
run exhausted its conflict budget without a verdict. That stronger result
has NOT received the solver-free replay or a second completed solver check;
it is recorded separately and not promoted to the agreed radius-4 result.

This finite replay is not a Lean kernel certificate. The supplied code and
counts make the excluded neighborhoods explicit and reproducible. Neither
r5(117) nor r5(118) is settled here.

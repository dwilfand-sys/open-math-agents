# Unrestricted r5(117): computational checkpoint

28 November 2026, live cycle begun 21:03 Israel. Work by Codex for
@dwilfand-sys, following Claude's Directive 10. No new extremal value is
claimed at this checkpoint.

## Exact models

`work/r5_sat.py` uses CaDiCaL 1.9.5 through python-sat. The primary variables
are membership bits for all 117 integers. It asserts exactly 69 selected
points, excludes every one of the 1,653 five-term arithmetic progressions,
and adds sound arithmetic-window cardinality bounds. Selected windows
are enough for redundant propagation; the five-term clauses alone enforce
progression-freeness. Reflection is broken by an exact lexicographic
comparison of the membership vector with its reversal. No structural
assumption on the set is made. Model: 2,139,292 variables, 3,212,296 clauses,
2,833 selected longer arithmetic windows, plus prefix/suffix bounds.

`work/r5_cp.py` is independently written, using OR-Tools CP-SAT. Its primary
variables indicate omitted points; exactly 48 are omitted. Every arithmetic
window of length 5 through 116 has at least `length-r5(length)` holes.
This includes every five-term progression. Reflection is broken by comparing
the numbers of holes in the two halves, not by copying the SAT encoding.

Both use the OEIS A003004 table through 115, downloaded from
https://oeis.org/A003004/b003004.txt, and the supplied bound r5(116)=68.
Consequently an infeasibility result would depend on those input upper
bounds. A returned witness is independently checked directly against every
five-term progression and would not depend on the table. Neither model
assumes the newer residue-profile exclusions posted by other workers.

Both passed the controls r5(24)<18 and r5(25)>=18. Their positive witnesses
were rechecked by direct progression enumeration. This checks basic encoding
behavior; it does not certify the full 117-point computation.

## Search budget and status

The SAT run is capped at 5,400 seconds measured at conflict-budget checkpoints.
The CP-SAT run is capped at 2,700 seconds with two workers. These are about
three CPU-hours in total, excluding small setup overhead. The SAT time check
is not an asynchronous hard interrupt: a single conflict-budget segment can
overrun, so its process must be monitored.

At this checkpoint both runs are active and neither has returned SAT or
UNSAT. There is no closed-tree count yet. A timeout or a large conflict count
will not be reported as a disproof. No Lean certificate is produced by these
programs. The exact numerical question remains 68 versus 69.

Live desk note #189768 announces the unrestricted searches. Matching lease:
56fc08bc-3cfd-45d3-baee-db0a1f040644. Heartbeat succeeded after Python urllib
POST requests were rejected by the site's HTTP filter; curl POST worked.

## Existing exclusions and attribution

Claude supplied the exclusions for two long residue classes both of size 17
and for asymmetric pairs inside a single distance group. The present models
do not impose either exclusion and therefore cover their complement too.
The precise earlier distance-group classification has not been recovered in
this container; it must not be silently strengthened to a general exclusion.

The live board now also contains @witeg4 #189119: an exhaustive exclusion of
all minimum-residue-size-six profiles, extending @jacklarmer #180510 and
@yhay81's earlier work. That is another worker's computational result, not
ours, and it is not used in either model.

@yhay81 #188986 reports an incomplete unrestricted DFS: 7 of 2,137 subtrees
closed after 5.9e8 nodes, with the remaining 2,130 uncovered. This motivates
trying different SAT/CP formulations, not treating their search as complete.

For the separate partial-cycle recurrence, Claude identified
@roshanasingh4 #132132 as prior p=3 work. Desk note #189768 now explicitly
credits that precedent and labels our #186131/#187469/#187728 as modular
Lean components/general-prime composition, without claiming first discovery
of p=3. The older note itself is outside the board's last-30-note feed;
this attribution is based on Claude's report, not a newly inspected copy.

The requested earlier three-hole-mask and semicircle notes have not been
recovered from the local files or identified fork branches. No replacement
statement has been invented, and no duplicate DONE note has been posted.

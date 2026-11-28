# An exact obstruction to the window-cap linear relaxation

28 November 2026. Codex for @dwilfand-sys. This is a limitation of a proof
method, not a solution of r5(117) or r5(118), and not a first-discovery claim.
The finite upper bounds used here are OEIS A003004 through 115, together
with r5(116)<=68. No other worker's search exclusions are assumed.

## Result

Even imposing every arithmetic-progression window cap, the forced endpoints,
the total cardinality, and reflection symmetry, the linear relaxation has
an exact rational feasible point of weight 69 on [1,117] and one of weight
70 on [1,118]. Hence no nonnegative linear combination of just these
constraints can exclude either candidate cardinality. This includes the
lower corridors and complement-window cuts derived from those constraints.

For 117, assign weight 1 to 1,2,116,117 and weight 65/113 elsewhere.
The total is exactly 69.

For 118, assign weight 1 to 1,2,3,116,117,118; weight 1/2 to 4,5,114,115;
and weight 31/54 to every other point. The total is exactly 70.

These are fractional weights, NOT progression-free sets. Both assignments
are invariant under reflection i -> N+1-i.

## Proof for 117

An arithmetic window of length m<=115 contains at most two weight-one
points. For step 1 this follows from its span; for a larger step it contains
at most one point of each adjacent endpoint pair. Thus for m>=2 its weight
is at most 2+(m-2)*65/113, which is <=r5(m) for every 2<=m<=115 by the
115-entry input table. A singleton has weight at most one. A length-116
window must have step 1; it has three weight-one points and 113 other
points, so its weight is exactly 68.

## Proof for 118

For 6<=m<=114, an arithmetic window contains at most three weight-one
points. For step 1, containing points from both endpoint triples cannot
give four unless its length is at least 116. For step 2, the two triples
supply at most three points of either parity. For step >=3, each triple
supplies at most one point. Consequently its weight is at most
3+(m-3)*31/54, which is <=r5(m) for 6<=m<=114 by the input table.

For length 5, a window with at most two weight-one points has weight at
most 2+3*(31/54)<4. A five-point window with three weight-one points must
be {1,2,3,4,5} or {114,115,116,117,118}; each has weight exactly 4.
For lengths at most 4, each individual weight is at most 1 and r5(m)=m.

A length-115 or length-116 window has step 1. Every length-115 window has
three weight-one points, four half-weight points and 108 points of weight
31/54, giving 67. Every length-116 window has four weight-one points,
four half-weight points and the same 108 middle points, giving 68.

## Independent exact audits

The Python Fraction checker enumerated every AP window of length <=116:
43,830 instances for N=117 and 44,640 for N=118, including repeated
singleton descriptions. All inequalities and both total weights passed.
A separately written C++ checker uses scaled integers (denominators 113
and 54), enumerates full residue rows and all their contiguous subwindows,
and obtains the same two counts with no failed inequality. It also checks
every scalar table comparison used in the proof above.

No floating-point LP, SAT verdict, or Lean kernel claim is needed for this
finite rational obstruction. The separate pair-moment relaxation adds
constraints outside this first-level cone; its numerical status is recorded
separately and remains insufficient for an extremal-value claim.

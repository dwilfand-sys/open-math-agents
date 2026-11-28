# Recovery correction, 28 November 2026

The process-state descriptions below are historical. The previous processes
were interrupted: native117 checkpoint UNKNOWN at 1778.66 s; native118 full
checkpoint UNKNOWN at 444.66 s; CP117 wrote no final verdict. No difficult
new prefix case was excluded. This recovery completed fresh bounded 420-second
CP and native searches; both returned UNKNOWN. CP reported 1,864,410
branches and 718,827 conflicts; native reported 1,120,095 conflicts and
1,605,309 decisions. No new hard case was closed.

The exact fractional obstruction in fractional-obstruction.md proves that
the ordinary all-window linear relaxation cannot settle either candidate.
It does not invalidate the integer search models: those retain Boolean
integrality, which the fractional construction deliberately relaxes.

--- Historical search coverage ---

# Exact scope of the partial searches

28 November 2026. No new value of r5(117) or r5(118) is established.

## 117-point search

Both exact formulations remain running under their fixed time limits.
The native SAT run's 64 disjoint cases fix the six membership bits at
positions 3,4,5,6,7,8, in that order, with 0 meaning omitted. It has closed
only cases 0--7, 31, and 56--63. All 17 closures have elementary reasons:

- Bits 3,4,5 cannot all vanish. The prefix of length 5 has at least
  69-r5(112)=3 points and already contains 1,2.
- Bits 3,4,5 cannot all be 1, because 1,2,3,4,5 would be a progression.
- Prefix 011111 contains the progression 4,5,6,7,8.

Thus no difficult new case has been closed; the other 47 prefixes remain.
Conflict counts are solver statistics, not counts of independently certified
closed subtrees.

Separately, assume the OTHER WORKERS' residue exclusions cited in the
directive and live board: all five residue sizes are at least seven
(@witeg4 #189119), and the two long residues cannot both have size 17
(@jacklarmer #180510). In residue order 0,1,2,3,4 modulo 5, the upper
bounds are (16,17,17,16,16), and sizes sum to 69. Reflection acts as
(c0,c1,c2,c3,c4)->(c3,c2,c1,c0,c4).

Exactly 2,170 labelled profiles, or 1,095 up to reflection, meet these
numerical conditions. Counts up to reflection by minimum residue size:
7:66; 8:110; 9:173; 10:246; 11:278; 12:186; 13:36.
The exact list is in r5-117-profiles.json. This is a profile enumeration,
not an exclusion of these profiles. The unavailable earlier asymmetric-pair
condition concerns configurations inside profiles; it is not assumed to
eliminate any entire profile here. Both main searches remain unrestricted
and do not rely on the other workers' exclusions.

## 118-point pilot

The CP-SAT pilot returned UNKNOWN after 600.363 seconds, reporting 1,454,938
branches and 146,142 conflicts. This is neither a proof nor a witness.
The native-cardinality pilot with complement cuts returned UNKNOWN after
about 401 seconds, with 1,030,083 conflicts. An earlier native pass without
these cuts was interrupted without a verdict.

All 44 closed prefix cases are elementary: position 3 is forced; 4 and 5
cannot both be present; and 4,5,6 cannot all be absent because the first
six sites need at least 70-r5(112)=4 points. The remaining 20 prefixes are
1001**, 101***, and 110***. Stars are independent binary choices. No
difficult new case has been excluded.

An unpartitioned native-cardinality run is continuing with a 1,800-second
limit. Its source has --split-bits 0, so it can search across all these
cases without repeatedly changing assumptions. This is another run of the
same SAT formulation, not a third independent verification method.

@RubberDuckDebug316's #190882 witness with mask
0x7b1e2f5254473d6d2b9ab79dcd5bce was independently checked: 69 points in
[1,118], no five-term progression. It is their construction; their reported
Lean result was not independently rerun here.

If 117 is proved to have maximum 68, then 118 has maximum 69 immediately:
delete the last site of any 70-point 118-set to obtain a 69-point 117-set.
Conversely, any 70-point 118-witness would settle both values, since the
known upper bound for 117 is 69. Neither direction supplies a new result
without settling the remaining feasibility question.

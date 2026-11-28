import OMAReductions.R_ResearchErdos142UnitThree25_R1
import Std.Tactic.BVDecide

/- Codex for @dwilfand-sys. The finite implication encodes the extremal
case of a cyclic three-term progression with step prime to five. -/
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_ResearchErdos142UnitThree25_R1.H1 := by
  intro m
  unfold OMA.R_ResearchErdos142UnitThree25_R1.threeFree OMA.R_ResearchErdos142UnitThree25_R1.population OMA.R_ResearchErdos142UnitThree25_R1.twoResidues
  bv_decide

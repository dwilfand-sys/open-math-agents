import Mathlib

namespace OMA.R_ResearchErdos142DivisorDefect_R1

/-- Sharp residue defect for a cyclic window against a divisor period. -/
def H1 : Prop := ∀ (L g : ℕ), 0 < L → 0 < g →
  let b := L % g
  let h := Nat.gcd L g
  b * (g - b) ≤ L * (g - h) ∧
    (b * (g - b) = L * (g - h) ↔ g ∣ L ∨ L ∣ g)

end OMA.R_ResearchErdos142DivisorDefect_R1

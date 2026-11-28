import Mathlib

/-! Uniform finite orbit averaging. A table row represents a direction
and translation permutation of an orbit; the transport axiom is the usual
column reindexing under a transitive group of transformations. -/
namespace OMA.R_ResearchErdos142OrbitAveraging_R1

def H1 : Prop := ∀ (R D : ℕ) (row : Fin R → Equiv.Perm (Fin D)),
  (∀ x y, ∃ tr : Equiv.Perm (Fin R), ∀ g, row (tr g) x=row g y) →
  ∀ (w : Fin D → ℤ) (x : Fin D),
    (D:ℤ)*(∑ g, w (row g x))=(R:ℤ)*(∑ y, w y)

end OMA.R_ResearchErdos142OrbitAveraging_R1

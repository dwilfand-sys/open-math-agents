import FormalConjectures.ErdosProblems.«142»

/- Fork-only specification for a finite cyclic certificate beside Erdős 142.
   Both statements below quantify over all starts and all allowable steps.
   The lower statement covers even repeated choices of the three holes. -/
namespace OMA.R_ResearchErdos142Mask49_R1

def point (a d : Fin 49) (j : ℕ) : Fin 49 := a + (j : Fin 49) * d

def H1 : Prop :=
  (∀ a d : Fin 49, d.val % 7 ≠ 0 → ∃ j : Fin 28,
    point a d j.val = 0 ∨ point a d j.val = 7 ∨ point a d j.val = 21) ∧
  (∀ x y z : Fin 49, ∃ a d : Fin 49, d.val % 7 ≠ 0 ∧ ∀ j : Fin 27,
    point a d j.val ≠ x ∧ point a d j.val ≠ y ∧ point a d j.val ≠ z)

end OMA.R_ResearchErdos142Mask49_R1

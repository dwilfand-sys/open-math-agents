import Mathlib

/-!
# Square roots of two in a finite rational group algebra and its augmentation ideal

Hugo MTV asks about both units. In the augmentation ideal the zero algebra of
the trivial group gives a degenerate example. This formulation records exactly
which finite groups have a root, including the nontrivial case raised by the
author after JP McCarthy's comment. Fork research statement for both questions.

Source: https://mathoverflow.net/questions/428070
Credit: @dwilfand-sys. Claude Code formalized the first question.
-/

namespace OMA.S_mo_428070

noncomputable section

def augmentation (G : Type) [Group G] : MonoidAlgebra ℚ G →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ G (1 : G →* ℚ)

def average (G : Type) [Group G] [Fintype G] : MonoidAlgebra ℚ G :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, MonoidAlgebra.single g (1 : ℚ)

theorem main : ∀ (G : Type) [Group G] [Fintype G],
    (¬ ∃ x : MonoidAlgebra ℚ G, x^2 = 2) ∧
    ((∃ x : MonoidAlgebra ℚ G,
        augmentation G x = 0 ∧ x^2 = (2:ℚ) • (1 - average G)) ↔ Subsingleton G) := by
  sorry

end

end OMA.S_mo_428070

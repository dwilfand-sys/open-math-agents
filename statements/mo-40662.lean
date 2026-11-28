import Mathlib

/-!
# A diagonal identity for a symplectic matrix over the two-element field

Robert Gunning asked whether this sum of entries of the four square blocks
vanishes for every symplectic matrix over the field with two elements.

Source: https://mathoverflow.net/questions/40662/symplectic-matrices
Credit: @dwilfand-sys (formalization by Codex)
-/

namespace OMA.S_mo_40662

theorem main : ∀ (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) (ZMod 2)),
    Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup (Fin n) (ZMod 2) →
    (∑ i, ∑ j, ∑ k, A i j * B i j * C i k * D i k) = 0 := by
  sorry

end OMA.S_mo_40662

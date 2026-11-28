import OMAReductions.R_ResearchErdos142ColumnKernel_R1
import Mathlib

/-! Periodic equal-width bins for a lifted mask. Bin labels computed by
division and reduction modulo q are periodic with physical period q*L. -/
namespace OMA.R_ResearchErdos142ShearMajority_R1

def bin (q L o u x : ℕ) : ℕ := ((o+u*x)/L)%q

def H1 : Prop :=
  ∀ (p t L : ℕ), p.Prime → 0 < t → 0 < L → p ∣ L →
  ∀ pos : Fin (p^t+1) → Fin (p^t*L),
    (∀ u : ℕ, Nat.Coprime u (p^t*L) → ∀ (o : ℕ) (b : Fin (p^t)),
      ∃ i, bin (p^t) L o u (pos i).val = b.val) →
    (∀ i k, (pos i).val % p = (pos k).val % p) ∨
    ∃ a : Fin (p^t+1), ∃ r : ℕ, r < L ∧
      (∀ i, i ≠ a → (pos i).val % p ≠ (pos a).val % p) ∧
      (∀ i, i ≠ a → (pos i).val % L = r) ∧
      (∀ b : Fin (p^t), ∃ i, i ≠ a ∧ (pos i).val = b.val*L+r)

end OMA.R_ResearchErdos142ShearMajority_R1

import Mathlib

/-! General finite inverse-moment implication for residual prime-power grids.
The hypotheses use exact raw integer moments, without rounding. A row is one
direction, with the ordered windows in that direction encoded by consecutive
indices. Site weights, coset totals and window counts are arbitrary finite data.
The cyclic derivation of those moments is a separate statement. -/
namespace OMA.R_ResearchErdos142GridMoment_R1

def total {n : ℕ} (f : Fin n → ℕ) : ℤ := ∑ i, (f i : ℤ)
def squares {n : ℕ} (f : Fin n → ℕ) : ℤ := ∑ i, (f i : ℤ)^2
def energy {u v : ℕ} (X : Fin u → Fin v → ℕ) : ℤ := ∑ i, squares (X i)

def H1 : Prop :=
  ∀ (q r k N C u v : ℕ), 2≤q → r*r≤q → 0<u → 0<v →
  ∀ (w : Fin N → ℕ) (W : Fin C → ℕ) (X : Fin u → Fin v → ℕ),
  total w = (k:ℤ)*q+r → total W = total w →
  (∀ c, W c≤r) →
  (∀ i j, k≤X i j ∧ X i j≤k+r) →
  (∀ i, (q:ℤ)*total (X i)=(v:ℤ)*total w) →
  (q:ℤ)^2 * energy X = (u:ℤ)*v * ((total w)^2 + (q:ℤ)*squares w-squares W) →
  ((∀ x, w x≤1) → ∀ (i : Fin u) (j l : Fin v), l.val=j.val+1 →
      X i j≤X i l+1 ∧ X i l≤X i j+1) →
  k=0

end OMA.R_ResearchErdos142GridMoment_R1

import Mathlib

/-! Removing the binomial coefficients from the finite hypergraph incidence bound.
This is the numerical step used to convert a cyclic extremal estimate to a count. -/
namespace OMA.R_ResearchErdos142SupersaturationPower_R1

def H1 : Prop := ∀ (k t m R E : ℕ), k ≤ t → t ≤ m →
  (t-R) * m.choose t ≤ E * (m-k).choose (t-k) →
  (t-R) * m^k ≤ E * t^k

end OMA.R_ResearchErdos142SupersaturationPower_R1

import Mathlib

/-! Exact weighted variance from the two-site incidence rule for a
transversal window design. Counts are unnormalized integer finite sums. -/
namespace OMA.R_ResearchErdos142WeightedSecond_R1

def mass {C B : ℕ} (w : Fin C → Fin B → ℤ) : ℤ := ∑ c, ∑ b, w c b
def sitesSq {C B : ℕ} (w : Fin C → Fin B → ℤ) : ℤ := ∑ c, ∑ b, (w c b)^2
def classesSq {C B : ℕ} (w : Fin C → Fin B → ℤ) : ℤ := ∑ c, (∑ b, w c b)^2
def weight {R C B : ℕ} (I : Fin R → Fin C → Fin B → ℤ)
    (w : Fin C → Fin B → ℤ) (j : Fin R) : ℤ := ∑ c, ∑ b, I j c b * w c b

def H1 : Prop := ∀ (R C B q : ℕ) (I : Fin R → Fin C → Fin B → ℤ),
  (∀ c b d e, (q:ℤ)^2*(∑ j, I j c b * I j d e) =
    (R:ℤ)*(if c≠d then 1 else if b=e then q else 0)) →
  ∀ (w : Fin C → Fin B → ℤ), (q:ℤ)^2*(∑ j, (weight I w j)^2) =
    (R:ℤ)*((mass w)^2+(q:ℤ)*sitesSq w-classesSq w)

end OMA.R_ResearchErdos142WeightedSecond_R1

import Mathlib

/-! Pair incidence in actual translated length-L windows on a prime-power circle.
The hypotheses exhibit the valuation of a difference outside the order-q coset. -/
namespace OMA.R_ResearchErdos142CyclicIncidence_R1

def hit {q L : ℕ} (z : ZMod (q*L)) : ℤ := if z.val < L then 1 else 0

noncomputable def unitWeight {N : ℕ} (u : ZMod N) : ℤ := by
  classical exact if IsUnit u then 1 else 0

def H1 : Prop := ∀ (p s q L g K : ℕ) [NeZero q] [NeZero L] [NeZero (q*L)],
  p.Prime → 0<s → q*L=p^s → L=p*K*g →
  ∀ (b : (ZMod (q*L))ˣ) (d : ZMod (q*L)), d=g*(b : ZMod (q*L)) →
    (∀ a : ZMod (q*L),
      (q:ℤ) * (∑ u : ZMod (q*L), unitWeight u * hit (a+u*d)) =
        ∑ u : ZMod (q*L), unitWeight u) ∧
    (q:ℤ)^2 * (∑ a : ZMod (q*L), ∑ u : ZMod (q*L),
      unitWeight u * hit a * hit (a+u*d)) =
        ((q*L:ℕ):ℤ) * (∑ u : ZMod (q*L), unitWeight u)

end OMA.R_ResearchErdos142CyclicIncidence_R1

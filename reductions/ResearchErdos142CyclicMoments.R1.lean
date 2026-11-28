import Mathlib

/-! Pair incidence in actual translated length-L windows on a prime-power circle.
The hypotheses exhibit the valuation of a difference outside the order-q coset. -/
namespace OMA.R_ResearchErdos142CyclicMoments_R1

def hit {q L : ℕ} (z : ZMod (q*L)) : ℤ := if z.val < L then 1 else 0

noncomputable def unitWeight {N : ℕ} (u : ZMod N) : ℤ := by
  classical exact if IsUnit u then 1 else 0

def Factored : Prop := ∀ (p s q L g K : ℕ) [NeZero q] [NeZero L] [NeZero (q*L)],
  p.Prime → 0<s → q*L=p^s → L=p*K*g →
  ∀ (b : (ZMod (q*L))ˣ) (d : ZMod (q*L)), d=g*(b : ZMod (q*L)) →
    (∀ a : ZMod (q*L),
      (q:ℤ) * (∑ u : ZMod (q*L), unitWeight u * hit (a+u*d)) =
        ∑ u : ZMod (q*L), unitWeight u) ∧
    (q:ℤ)^2 * (∑ a : ZMod (q*L), ∑ u : ZMod (q*L),
      unitWeight u * hit a * hit (a+u*d)) =
        ((q*L:ℕ):ℤ) * (∑ u : ZMod (q*L), unitWeight u)

def H1 : Prop := ∀ (p t l : ℕ) [NeZero p], p.Prime →
  (∀ (d : ZMod (p^t*p^l)), ¬p^l∣d.val → ∀a : ZMod (p^t*p^l),
    ((p^t:ℕ):ℤ) * (∑u : ZMod (p^t*p^l),unitWeight u*hit (a+u*d)) =
      ∑u : ZMod (p^t*p^l),unitWeight u) ∧
  (∀ x y : ZMod (p^t*p^l),
    ((p^t:ℕ):ℤ)^2 * (∑a : ZMod (p^t*p^l), ∑u : ZMod (p^t*p^l),
      unitWeight u*hit (a+u*x)*hit (a+u*y)) =
    ((p^t*p^l:ℕ):ℤ) * (∑u : ZMod (p^t*p^l),unitWeight u) *
      (if y-x=0 then ((p^t:ℕ):ℤ) else if p^l∣(y-x).val then 0 else 1)) ∧
  (∀ w : ZMod (p^t*p^l) → ℤ,
    ((p^t:ℕ):ℤ)^2 * (∑a : ZMod (p^t*p^l), ∑u : ZMod (p^t*p^l),
      unitWeight u*(∑x,hit (a+u*x)*w x)^2) =
    ((p^t*p^l:ℕ):ℤ) * (∑u : ZMod (p^t*p^l),unitWeight u) *
      ((∑x,w x)^2 + ((p^t:ℕ):ℤ)*(∑x,w x^2) -
        ∑x,∑y,if p^l∣(y-x).val then w x*w y else 0))

end OMA.R_ResearchErdos142CyclicMoments_R1

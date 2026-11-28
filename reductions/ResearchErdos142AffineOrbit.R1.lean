import Mathlib

/-! An actual affine automorphism of Z/(p^(e+h)) taking two prescribed
ordered sites to two others, when their modular differences have valuation e.
The unit-factor representation of the differences uses the quotient p^h. -/
namespace OMA.R_ResearchErdos142AffineOrbit_R1

def H1 : Prop := ∀ (p e h a b : ℕ), p.Prime → 0<h → ¬p∣a → ¬p∣b →
  ∀ x y z w : ZMod (p^(e+h)),
    y-x=(p^e*a : ℕ) → w-z=(p^e*b : ℕ) →
    ∃ u : ℕ, u<p^h ∧ u.Coprime (p^(e+h)) ∧
      ∃ shift : ZMod (p^(e+h)), (u : ZMod (p^(e+h)))*x+shift=z ∧
        (u : ZMod (p^(e+h)))*y+shift=w

end OMA.R_ResearchErdos142AffineOrbit_R1

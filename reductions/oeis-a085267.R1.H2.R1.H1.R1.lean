import OMAReductions.R_oeis_a085267_R1_H2_R1
import Mathlib

/-!
# The intermediate interval for A085267

Source: https://oeis.org/A085267
Credit: @dwilfand-sys
The numerical sieve bound leaves more than one candidate after all estimated
losses. A failure to find two representations produces the opposite inequality.
-/

open scoped BigOperators

namespace OMA.R_oeis_a085267_R1_H2_R1_H1_R1

open OMA.S_oeis_a085267

def H1 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 300 ≤ J → J ≤ 1000000 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H2 : Prop := ∀ n : ℕ, 365000 < n → n ≤ 4000000000000 →
    representations n < 2 →
    ∃ (J : ℕ) (S : Finset ℕ), 300 ≤ J ∧ J ≤ 1000000 ∧
      (∀ p ∈ S, 2 < p ∧ p.Prime) ∧ (∏ p ∈ S, p) ≤ 2*J+2 ∧
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ)) ≤
        ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
          (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1)))

theorem main : H1 → H2 → OMA.R_oeis_a085267_R1_H2_R1.H1 := by
  intro budget cover n hlo hhi
  by_contra! hfail
  obtain ⟨J,S,hJ,hJ',hS,hprod,hcount⟩ := cover n hlo hhi hfail
  exact (not_lt_of_ge hcount) (budget J S hJ hJ' hS hprod)

end OMA.R_oeis_a085267_R1_H2_R1_H1_R1

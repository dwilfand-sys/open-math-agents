import OMAReductions.R_oeis_a085267_R1_H2_R1_H1_R1
import Mathlib

/-!
Four consecutive intervals for the A085267 strict sieve bound.
Source: https://oeis.org/A085267
Credit: @dwilfand-sys
-/

open scoped BigOperators
namespace OMA.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R1

def H1 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 300 ≤ J → J ≤ 111355 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H2 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 111356 ≤ J → J ≤ 372019 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H3 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 372020 ≤ J → J ≤ 740049 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H4 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 740050 ≤ J → J ≤ 1000000 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

theorem main : H1 → H2 → H3 → H4 → OMA.R_oeis_a085267_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2 h3 h4 J S hlo hhi hS hprod
  by_cases first : J ≤ 111355
  · exact h1 J S hlo first hS hprod
  by_cases second : J ≤ 372019
  · exact h2 J S (by omega) second hS hprod
  by_cases third : J ≤ 740049
  · exact h3 J S (by omega) third hS hprod
  exact h4 J S (by omega) hhi hS hprod

end OMA.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R1

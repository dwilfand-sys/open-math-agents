import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1
import Mathlib

/-! Separate the same-row cost estimate, including each small exceptional-prime refund,
from the finite numerical profiles of the intermediate A085265 proof.
Proof development by Codex for @dwilfand-sys. Root statement by @niclorusso. -/

open Finset
namespace OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R5

def H1 : Prop := ∀ (J : ℕ) (S A : Finset ℕ) (α R : ℚ), 300 ≤ J →
    (let P := (Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)
    A ⊆ S ∧ A ⊆ ({3,5,7,11,13,17} : Finset ℕ) ∧ (P.card : ℚ) ≤ α*(J:ℚ) ∧
    ((J ≤ 420 ∧ R = 96911/500000) ∨ (J ≤ 599 ∧ R = 49013/250000) ∨
     (J ≤ 1023 ∧ R = 98959/500000) ∨ (J ≤ 2047 ∧ R = 199283/1000000) ∨
     (J ≤ 4095 ∧ R = 200323/1000000) ∨ R = 41/200)) →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
       (2*J/(p^2)+1) : ℕ) : ℚ) ≤ (J:ℚ)*(α+2*(R-(∑ p ∈ A, 1/(p:ℚ)^2)))-(A.card:ℚ)

def H2 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 300 ≤ J → J ≤ 1000000 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ∃ (A : Finset ℕ) (α R : ℚ), (let P := (Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)
    A ⊆ S ∧ A ⊆ ({3,5,7,11,13,17} : Finset ℕ) ∧ (P.card : ℚ) ≤ α*(J:ℚ) ∧
    ((J ≤ 420 ∧ R = 96911/500000) ∨ (J ≤ 599 ∧ R = 49013/250000) ∨
     (J ≤ 1023 ∧ R = 98959/500000) ∨ (J ≤ 2047 ∧ R = 199283/1000000) ∨
     (J ≤ 4095 ∧ R = 200323/1000000) ∨ R = 41/200)) ∧
      ∀ w : ℚ, w ≤ (J:ℚ)*(α+2*(R-(∑ p ∈ A, 1/(p:ℚ)^2)))-(A.card:ℚ) →
      w + (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) <
      (J:ℚ)*(∏ p ∈ S, (1-1/(p:ℚ)))

set_option maxHeartbeats 1500000 in
theorem main : H1 → H2 → OMA.R_oeis_a085265_R2_H2_R1_H1_R1.H1 := by
  intro cost witness J S hlo hhi hS hprod
  obtain ⟨A,α,R,ha,margin⟩ := witness J S hlo hhi hS hprod
  exact margin _ (cost J S A α R hlo ha)

end OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R5

import OMAReductions.R_oeis_a085264_R1
import Mathlib

/-!
The 101-representation cutoff for A085264, from J = 1,600.
Source: https://oeis.org/A085264
Credit: @dwilfand-sys
The finite sieve budget keeps one hundred units of slack. The second
hypothesis converts any counterexample to an exceptional-prime set violating
that budget. Above four trillion the independent large-range sieve suffices.
-/

open scoped BigOperators
namespace OMA.R_oeis_a085264_R1_H2_R1

open OMA.S_oeis_a085264

def H1 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 1600 ≤ J → J ≤ 1000000 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
      (2*J/(p^2)+1) : ℕ) : ℚ) + (100 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H2 : Prop := ∀ n : ℕ, 10252804 < n → representations n ≤ 100 →
    ∃ (J : ℕ) (S : Finset ℕ), 1600 ≤ J ∧ J ≤ 1000000 ∧
      (∀ p ∈ S, 2 < p ∧ p.Prime) ∧ (∏ p ∈ S, p) ≤ 2*J+2 ∧
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ)) ≤
        ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
          (2*J/(p^2)+1) : ℕ) : ℚ) + (100 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1)))

theorem main : H1 → H2 → OMA.R_oeis_a085264_R1.H2 := by
  intro budget cover n hlo
  by_contra! hfail
  obtain ⟨J,S,hJ,hJ',hS,hprod,hcount⟩ := cover n hlo hfail
  exact (not_lt_of_ge hcount) (budget J S hJ hJ' hS hprod)

end OMA.R_oeis_a085264_R1_H2_R1

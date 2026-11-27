import OMAReductions.R_oeis_a085265_R2_H2_R1
import Mathlib

/-!
A finite numerical sieve budget and the covering argument for the intermediate
range of A085265. If every candidate root fails, counting excluded roots must
give an obstruction at least as large as the lower bound on candidates.
The numerical statement rules out that inequality without reference to n.
Credit: @dwilfand-sys. Root statement formalized by @niclorusso.
-/

open scoped BigOperators

namespace OMA.R_oeis_a085265_R2_H2_R1_H1_R1

def H1 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 300 ≤ J → J ≤ 1000000 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) < (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H2 : Prop := ∀ n : ℕ, 365000 < n → n ≤ 4000000000000 →
    (∀ k : ℕ, 0 < k → k^2 < n → ¬ Squarefree (n-k^2)) →
    ∃ (J : ℕ) (S : Finset ℕ), 300 ≤ J ∧ J ≤ 1000000 ∧
      (∀ p ∈ S, 2 < p ∧ p.Prime) ∧ (∏ p ∈ S, p) ≤ 2*J+2 ∧
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ)) ≤ ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))

theorem main : H1 → H2 → OMA.R_oeis_a085265_R2_H2_R1.H1 := by
  intro budget cover n hlo hhi
  by_contra none
  have fail (k : ℕ) (hk : 0 < k) (hkn : k^2 < n) : ¬ Squarefree (n-k^2) :=
    fun hs => none ⟨k,hk,hkn,hs⟩
  obtain ⟨J,S,hJ,hJ',hS,hprod,hcount⟩ := cover n hlo hhi fail
  exact (not_lt_of_ge hcount) (budget J S hJ hJ' hS hprod)

end OMA.R_oeis_a085265_R2_H2_R1_H1_R1

import OMAStatements.S_oeis_a085265
import Mathlib

/-!
Finite and infinite ranges for OEIS A085265, formalized by @niclorusso.
Proof prepared by Codex for @dwilfand-sys. This fork check isolates the
finite certificate in the full proof. Credit: @dwilfand-sys
-/

namespace A085265Sieve

theorem exclude_one_thirteen {n k : ℕ} (hk : 0 < k) (hkn : k^2 < n)
    (hs : Squarefree (n-k^2)) : n ≠ 1 ∧ n ≠ 13 := by
  have hk₁ : 0 < k^2 := pow_pos hk 2
  refine ⟨by omega,?_⟩
  rintro rfl
  have hsmall : k < 4 := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have table : ∀ j : Fin 4, 0 < j.val → ¬ Squarefree (13-j.val^2) := by decide +kernel
  exact table ⟨k,hsmall⟩ hk hs

end A085265Sieve

namespace OMA.R_oeis_a085265_R2

def H1 : Prop := ∀ n : ℕ, 0 < n → n ≤ 365000 → n ≠ 1 → n ≠ 13 →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

def H2 : Prop := ∀ n : ℕ, 365000 < n →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085265.main := by
  intro small large n hn
  constructor
  · rintro ⟨s,k,hs,hsf,hk,he⟩
    have hdiff : n-k^2 = s := by omega
    exact A085265Sieve.exclude_one_thirteen hk (by omega) (hdiff.symm ▸ hsf)
  · rintro ⟨h₁,h₁₃⟩
    have hex : ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2) := by
      by_cases h : n ≤ 365000
      · exact small n hn h h₁ h₁₃
      · exact large n (by omega)
    obtain ⟨k,hk,hkn,hs⟩ := hex
    exact ⟨n-k^2,k,by omega,hs,hk,by omega⟩

end OMA.R_oeis_a085265_R2

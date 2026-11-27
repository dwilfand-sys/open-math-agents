import OMAStatements.S_oeis_a085265
import Mathlib

/-!
The OEIS conjecture requires the square to be positive. Jiménez Urroz's theorem
allows a zero square, which only affects inputs that are themselves squarefree.
The second hypothesis uses positive even squares for large squarefree inputs.
The permitted small inputs have positive square roots at most five.

J. Jiménez Urroz, *Every integer can be written as a square plus a squarefree*,
Expositiones Mathematicae, DOI 10.1016/j.exmath.2021.12.002, Theorem 1.
-/

namespace A085265Sieve

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_table : ∀ n : Fin 401, n.val ≠ 0 → n.val ≠ 1 → n.val ≠ 13 →
    ∃ k : Fin 6, 0 < k.val ∧ k.val^2 < n.val ∧ Squarefree (n.val-k.val^2) := by
  decide +kernel

theorem squarefree_small {n : ℕ} (hn : 0 < n) (hN : n ≤ 400) (h₁ : n ≠ 1)
    (h₁₃ : n ≠ 13) : ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2) := by
  obtain ⟨k,hk⟩ := small_table ⟨n,by omega⟩ hn.ne' h₁ h₁₃
  exact ⟨k.val,hk⟩

theorem exclude_one_thirteen {n k : ℕ} (hk : 0 < k) (hkn : k^2 < n)
    (hs : Squarefree (n-k^2)) : n ≠ 1 ∧ n ≠ 13 := by
  have hk₁ : 1 ≤ k^2 := by positivity
  refine ⟨by omega,?_⟩
  rintro rfl
  have hsmall : k < 4 := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have table : ∀ j : Fin 4, 0 < j.val → ¬ Squarefree (13-j.val^2) := by decide
  exact table ⟨k,hsmall⟩ hk hs

end A085265Sieve

namespace OMA.R_oeis_a085265_R1

/-- Jiménez Urroz's square-plus-squarefree theorem, allowing the square zero. -/
def H1 : Prop := ∀ n : ℕ, 0 < n →
  ∃ s k : ℕ, 0 < s ∧ Squarefree s ∧ s+k^2=n

/-- Above 400, an even positive square suffices for every squarefree input. -/
def H2 : Prop := ∀ n : ℕ, 400 < n → Squarefree n →
  ∃ j : ℕ, 0 < j ∧ (2*j)^2 < n ∧ Squarefree (n-(2*j)^2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085265.main := by
  intro h₁ h₂ n hn
  constructor
  · rintro ⟨s,k,hs,hsf,hk,heq⟩
    have hlt : k^2 < n := by omega
    have hdiff : n-k^2 = s := by omega
    exact A085265Sieve.exclude_one_thirteen hk hlt (hdiff.symm ▸ hsf)
  · rintro ⟨he₁,he₁₃⟩
    suffices hr : ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2) by
      obtain ⟨k,hk,hkn,hsf⟩ := hr
      exact ⟨n-k^2,k,by omega,hsf,hk,by omega⟩
    by_cases hsmall : n ≤ 400
    · exact A085265Sieve.squarefree_small hn hsmall he₁ he₁₃
    by_cases hsf : Squarefree n
    · obtain ⟨j,hj,hjn,hs⟩ := h₂ n (by omega) hsf
      exact ⟨2*j,by omega,hjn,hs⟩
    · obtain ⟨s,k,hs,hss,hsk⟩ := h₁ n hn
      have hk : 0 < k := by
        by_contra! hz
        have hzero : k = 0 := by omega
        have hsn : s = n := by simpa [hzero] using hsk
        exact hsf (hsn ▸ hss)
      exact ⟨k,hk,by omega,(show n-k^2=s by omega).symm ▸ hss⟩

end OMA.R_oeis_a085265_R1

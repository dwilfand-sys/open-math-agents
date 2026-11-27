import OMAStatements.S_oeis_a085263
import Mathlib

/-!
# A085263, an effective bound and a finite zero-level question

Source: https://oeis.org/A085263
Credit: @dwilfand-sys

Robert G. Wilson v conjectured finiteness of each level of Reinhard
Zumkeller's representation-count sequence. An asymptotic in J. Jiménez
Urroz, Expositiones Mathematicae 40 (2022), §4, already implies finiteness.
The first step below asks for an explicit elementary uniform bound on every
sublevel. The second step is a finite assertion about the exceptional inputs.
-/

namespace OMA.R_oeis_a085263_R1

open OMA.S_oeis_a085263

def H1 : Prop := ∀ k n : ℕ, 0 < n → representations n ≤ k →
    n ≤ (2 * (100 * (k + 300000) + 15 * k ^ 2) + 2) ^ 2

def H2 : Prop := ∀ n : ℕ, 0 < n → n ≤ (2 * (100 * 300000) + 2) ^ 2 →
    representations n = 0 → n = 1 ∨ n = 13

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085263.main := by
  intro hbound hzero
  constructor
  · intro k
    apply (Set.finite_Iic ((2 * (100 * (k + 300000) + 15 * k ^ 2) + 2) ^ 2)).subset
    intro n hn
    obtain ⟨hp, he⟩ := hn
    exact hbound k n hp he.le
  · ext n
    change (0 < n ∧ representations n = 0) ↔ n ∈ ({1, 13} : Set ℕ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, he⟩
      exact hzero n hp (hbound 0 n hp he.le) he
    · rintro (rfl | rfl) <;> decide +kernel

end OMA.R_oeis_a085263_R1

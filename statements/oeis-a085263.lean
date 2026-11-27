import Mathlib

/-!
# Finite representation levels for positive square plus squarefree

Source: https://oeis.org/A085263
Credit: @dwilfand-sys

Reinhard Zumkeller defined A085263 on the positive integers in 2003.
Robert G. Wilson v conjectured in 2014 that each fixed representation count
occurs only finitely often and identified 1 and 13 as its zero level.
The 25 positive-level first occurrences starting at 2 and the 11 frequencies
starting at 2 in his comment are numerical data accompanying the conjecture.
Each representation is determined by the positive square root, and the
squarefree summand must also be positive.
-/

namespace OMA.S_oeis_a085263

def representations (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1)).filter
    (fun k => 0 < k ∧ k ^ 2 < n ∧ Squarefree (n - k ^ 2))).card

def level (k : ℕ) : Set ℕ := {n | 0 < n ∧ representations n = k}

theorem main :
    (∀ k : ℕ, (level k).Finite) ∧ level 0 = ({1, 13} : Set ℕ) := by
  sorry

end OMA.S_oeis_a085263

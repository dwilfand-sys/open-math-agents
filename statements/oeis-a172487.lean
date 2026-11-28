import Mathlib

/-!
# First differences in OEIS A172487

Source: https://oeis.org/A172487
Credit: @dwilfand-sys (Lean formalization by Codex). Giovanni Teofilatto
posed this question. The definitions of A172240 and A181669 follow their
OEIS entries. The difference at a term p is the next term minus p. Describing
consecutive terms by the absence of an intermediate member avoids assuming
in advance that the sequence is infinite.
-/

namespace OMA.S_oeis_a172487

/-- A181669 consists of primes of the form 6n-1 such that p-1 is a semiprime
and p+2 is a prime or the square of a prime. -/
def inA181669 (p : ℕ) : Prop :=
  p.Prime ∧ p % 6 = 5 ∧
    (∃ a b : ℕ, a.Prime ∧ b.Prime ∧ p - 1 = a * b) ∧
    ((p + 2).Prime ∨ ∃ r : ℕ, r.Prime ∧ p + 2 = r ^ 2)

/-- A172240 consists of odd primes outside A181669. A172487 retains the
lower members of twin prime pairs in that sequence. -/
def inA172487 (p : ℕ) : Prop :=
  p.Prime ∧ (p + 2).Prime ∧ Odd p ∧ ¬ inA181669 p

theorem main : ∀ p q : ℕ, inA172487 p → inA172487 q → 3 < p → p < q →
    (∀ r : ℕ, p < r → r < q → ¬ inA172487 r) → 6 ∣ q - p := by
  sorry

end OMA.S_oeis_a172487

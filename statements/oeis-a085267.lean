import Mathlib

/-!
# The eventually consecutive terms of A085267

Source: https://oeis.org/A085267
Credit: @dwilfand-sys

Reinhard Zumkeller defined this sequence in 2003. It lists in increasing
order, starting with index one, the positive integers with at least two
representations as a positive square plus a positive squarefree integer.
Charles R. Greathouse IV conjectured in 2011 that its nth term is n+11 for
n>50. Membership and the number of terms at most n+11 express this index.
-/

namespace OMA.S_oeis_a085267

def representations (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1)).filter
    (fun k => 0 < k ∧ k ^ 2 < n ∧ Squarefree (n - k ^ 2))).card

def termsThrough (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter
    (fun t => 0 < t ∧ 2 ≤ representations t)).card

theorem main : ∀ n : ℕ, 50 < n →
    2 ≤ representations (n + 11) ∧ termsThrough (n + 11) = n := by
  sorry

end OMA.S_oeis_a085267

import Mathlib

/-!
# Exceptions to subset sums of lucky-indexed lucky numbers

Source: https://oeis.org/A319824
Credit: @dwilfand-sys

Amiram Eldar conjectured in 2018 that this list has 98 terms and ends at 373.
Ranks are one-based. Removing every s-th term sends a retained rank x back
to rank x + (x - 1) / (s - 1) in the previous sieve. We invert the most
recent deletion first, then return to the odd numbers. Earlier ranks are
stable by the time the next lucky step is selected. The auxiliary value
at rank zero never contributes to a subset sum.
-/

namespace OMA.S_oeis_a319824

def liftRank (s x : ℕ) : ℕ := x + (x - 1) / (s - 1)

def rankValue (ss : List ℕ) (x : ℕ) : ℕ :=
  2 * ss.foldl (fun y s => liftRank s y) x - 1

def steps : ℕ → List ℕ
  | 0 => []
  | k + 1 => let ss := steps k
             rankValue ss (k + 2) :: ss

def lucky (n : ℕ) : ℕ := rankValue (steps (n - 2)) n

def u (n : ℕ) : ℕ := lucky (lucky n)

/-- The first k positive indices supply the available summands, each at most once. -/
def attainable : ℕ → ℕ → Prop
  | 0, x => x = 0
  | k + 1, x => attainable k x ∨ ∃ y, attainable k y ∧ x = y + u (k + 1)

def exceptions : Set ℕ := {x | 0 < x ∧ ¬ ∃ k, attainable k x}

theorem main : exceptions.Finite ∧ exceptions.ncard = 98 ∧ IsGreatest exceptions 373 := by
  sorry

end OMA.S_oeis_a319824

import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1

/-!
Twin-prime exceptions for McEachen's recurrence. The two recurrence lemmas
come from the accepted A135508 reductions by @harshshah1618 and @Hennyrick.
-/

namespace A135508Twins

open OeisA135508
open OMA.R_OeisA135508_conjecture_R1
open OMA.R_OeisA135508_conjecture_R1_H2_R1

/-- Every upper twin prime exceeding seven is exceptional. -/
theorem exceptional_of_twin {p : ℕ} (hp : p.Prime) (ht : (p - 2).Prime) (h7 : 7 < p) :
    a (p - 1) ≠ p := by
  have nonzero {v : ℕ} (hv : v.Prime) (h3 : 3 < v) : v % 3 ≠ 0 := by
    intro h
    rcases hv.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h) with h | h <;> omega
  have hmodp := nonzero hp (by omega)
  have hmodt := nonzero ht (by omega)
  have hmod : (p - 2) % 3 = 2 := by omega
  have h := prime_mod_three_two three_persists ht hmod (by omega)
  rw [show p - 2 - 1 = p - 3 by omega] at h
  exact fun eq => (prime_target_iff hp (by omega)).mp eq h

theorem small_cases :
    a (2 - 1) = 2 ∧ a (3 - 1) = 3 ∧ a (5 - 1) ≠ 5 ∧ a (7 - 1) = 7 := by
  decide

end A135508Twins

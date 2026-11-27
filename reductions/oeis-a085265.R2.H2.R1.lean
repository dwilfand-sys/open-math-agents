import OMAReductions.R_oeis_a085265_R2

/-! Split the remaining positive-square range at the start of the large sieve.
The root statement was formalized by @niclorusso. Credit: @dwilfand-sys. -/

namespace OMA.R_oeis_a085265_R2_H2_R1

def H1 : Prop := ∀ n : ℕ, 365000 < n → n ≤ 4000000000000 →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

def H2 : Prop := ∀ n : ℕ, 4000000000000 < n →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

theorem main : H1 → H2 → OMA.R_oeis_a085265_R2.H2 := by
  intro middle large n hn
  by_cases h : n ≤ 4000000000000
  · exact middle n hn h
  · exact large n (by omega)

end OMA.R_oeis_a085265_R2_H2_R1

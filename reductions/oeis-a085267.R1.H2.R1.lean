import OMAReductions.R_oeis_a085267_R1

/-!
Intermediate and large ranges for positive-square-plus-squarefree
representations in A085267. In the large range the proof supplies at
least 101 distinct roots. Charles R. Greathouse IV conjectured the
eventual index formula. Credit: @dwilfand-sys
Source: https://oeis.org/A085267
-/

namespace OMA.R_oeis_a085267_R1_H2_R1

open OMA.S_oeis_a085267

def H1 : Prop := ∀ n : ℕ, 365000 < n → n ≤ 4000000000000 →
  2 ≤ representations n

def H2 : Prop := ∀ n : ℕ, 4000000000000 < n → 101 ≤ representations n

theorem main : H1 → H2 → OMA.R_oeis_a085267_R1.H2 := by
  intro middle large n hn
  by_cases h : n ≤ 4000000000000
  · exact middle n hn h
  · exact (show 2 ≤ 101 by decide).trans (large n (by omega))

end OMA.R_oeis_a085267_R1_H2_R1

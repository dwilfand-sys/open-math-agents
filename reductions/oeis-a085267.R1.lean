import OMAStatements.S_oeis_a085267

/-!
# A085267: finite exceptions and the remaining tail

Source: https://oeis.org/A085267
Credit: @dwilfand-sys
Charles R. Greathouse IV proposed the eventual index formula. This reduction
separates a finite classification from the lower bound on the remaining inputs.
-/

namespace OMA.R_oeis_a085267_R1

open OMA.S_oeis_a085267

def H1 : Prop := ∀ n : ℕ, 0 < n → n ≤ 365000 →
  (representations n < 2 ↔ n ∈ ({1, 2, 3, 4, 5, 8, 9, 13, 25, 29, 61} : Finset ℕ))

def H2 : Prop := ∀ n : ℕ, 365000 < n → 2 ≤ representations n

lemma two_from_sixtytwo (h1 : H1) (h2 : H2) {n : ℕ} (hn : 62 ≤ n) :
    2 ≤ representations n := by
  by_cases hfinite : n ≤ 365000
  · have hne : n ∉ ({1, 2, 3, 4, 5, 8, 9, 13, 25, 29, 61} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    by_contra! h
    exact hne ((h1 n (by omega) hfinite).mp h)
  · exact h2 n (by omega)

lemma rank_from_sixtyone (h1 : H1) (h2 : H2) (m : ℕ) (hm : 61 ≤ m) :
    termsThrough m = m - 11 := by
  induction m, hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have hok := two_from_sixtytwo h1 h2 (n := m+1) (by omega)
    have hstep : termsThrough (m+1) = termsThrough m + 1 := by
      unfold termsThrough
      rw [Finset.range_add_one (m+1)]
      simp [Finset.filter_insert, hok]
    omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085267.main := by
  intro h1 h2 n hn
  refine ⟨two_from_sixtytwo h1 h2 (by omega), ?_⟩
  have h := rank_from_sixtyone h1 h2 (n+11) (by omega)
  omega

end OMA.R_oeis_a085267_R1

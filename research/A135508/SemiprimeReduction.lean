import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1

/-!
Elementary reduction of the A135508 witness problem to semiprimes.
The two hypotheses are explicit, so this is a reduction rather than a proof
of the remaining conjecture. For an explicit analytic envelope, see
Lamzouri, Li and Soundararajan, Corollary 1.2, and the accompanying note.
-/

namespace A135508Semiprimes

def Witness (n : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ∣ n ∧
    ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < n ∧ r % 3 = 2 ∧ q ∣ r + 2

def LeastPrimeBound (U : ℕ → ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → 1000000 < q →
    ∃ r : ℕ, r.Prime ∧ 5 < r ∧ r < q ^ 3 ∧ r ≤ U q ∧ r % 3 = 2 ∧ q ∣ r + 2

def SemiprimeCase (U : ℕ → ℕ) : Prop :=
  ∀ q s : ℕ, q.Prime → s.Prime → 1000000 < q → q < s →
    (q * s) % 3 = 2 → (q * s + 2).Prime → q * s ≤ U q → Witness (q * s)

private theorem square_mod_three_ne_two (q : ℕ) : (q * q) % 3 ≠ 2 := by
  have hq : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rw [Nat.mul_mod]
  rcases hq with h | h | h <;> rw [h] <;> decide

theorem of_semiprimes (U : ℕ → ℕ) (hap : LeastPrimeBound U)
    (hsem : SemiprimeCase U) : OMA.R_OeisA135508_conjecture_R1_H2_R1.H2 := by
  intro p hp h5 hmod hcomp hlarge
  let n := p - 2
  let q := n.minFac
  let s := n / q
  have hn : 0 < n := by dsimp [n]; omega
  have hnmod : n % 3 = 2 := by dsimp [n]; omega
  have hq : q.Prime := Nat.minFac_prime (by dsimp [n]; omega)
  have hqn : q ∣ n := Nat.minFac_dvd _
  have heq : q * s = n := Nat.mul_div_cancel' hqn
  have hqs : q ≤ s := Nat.minFac_le_div hn hcomp
  have hsn : s ∣ n := ⟨q, heq.symm.trans (Nat.mul_comm _ _)⟩
  change Witness n
  obtain ⟨r, hr, hr5, hcube, hupper, hmodr, hdiv⟩ := hap q hq hlarge
  by_cases htime : r < n
  · exact ⟨q, hq, hqn, r, hr, hr5, htime, hmodr, hdiv⟩
  · have hq2 : 2 ≤ q := hq.two_le
    have hs : s.Prime := by
      by_contra hc
      have hsf : s.minFac.Prime := Nat.minFac_prime (by omega)
      have hf : q ≤ s.minFac := Nat.minFac_le_of_dvd hsf.two_le ((Nat.minFac_dvd _).trans hsn)
      have hsq : q ^ 2 ≤ s := (Nat.pow_le_pow_left hf 2).trans
        (Nat.minFac_sq_le_self (by omega) hc)
      have hcn : q ^ 3 ≤ n := by
        rw [← heq, show q ^ 3 = q * q ^ 2 by ring]
        exact Nat.mul_le_mul_left q hsq
      omega
    have hlt : q < s := lt_of_le_of_ne hqs (by
      intro eq
      have hh : (q * s) % 3 = 2 := heq.symm ▸ hnmod
      rw [← eq] at hh
      exact square_mod_three_ne_two _ hh)
    have hp' : (q * s + 2).Prime := by
      have eq : q * s + 2 = p := by rw [heq]; dsimp [n]; omega
      exact eq.symm ▸ hp
    rw [← heq]
    exact hsem q s hq hs hlarge hlt (heq.symm ▸ hnmod) hp' (by omega)

end A135508Semiprimes

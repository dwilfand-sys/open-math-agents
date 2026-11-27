import Mathlib

namespace OMA.OddAlmost

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Every prime divisor of an almost-perfect number is coprime to its divisor sum. -/
theorem prime_not_dvd_sigma {n q : ℕ} (he : 1 + σ 1 n = 2 * n)
    (hq : q.Prime) (hqn : q ∣ n) : ¬ q ∣ σ 1 n := by
  intro hd
  have htot : q ∣ 1 + σ 1 n := by
    rw [he]
    exact dvd_mul_of_dvd_right hqn 2
  have hone : q ∣ 1 := by simpa using Nat.dvd_sub htot hd
  have hle := Nat.le_of_dvd (by decide : 0 < 1) hone
  have hge := hq.two_le
  omega

/-- Exclude the entire exponent assignment when a support prime divides a
geometric sum associated to any of the prime powers in the number. -/
theorem prime_not_dvd_geometric_factor {n p q : ℕ} (hn : 0 < n)
    (he : 1 + σ 1 n = 2 * n) (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) :
    ¬ q ∣ ∑ i ∈ range (n.factorization p + 1), p ^ i := by
  intro hd
  have hdiv : (∑ i ∈ range (n.factorization p + 1), p ^ i) ∣ σ 1 n := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne']
    simp only [mul_one]
    exact dvd_prod_of_mem (fun r => ∑ i ∈ range (n.factorization r + 1), r ^ i) hp
  exact prime_not_dvd_sigma he (Nat.prime_of_mem_primeFactors hq)
    (Nat.dvd_of_mem_primeFactors hq) (hd.trans hdiv)

/-- Every odd square that is almost perfect has divisor sum one modulo sixteen. -/
theorem sigma_mod_sixteen {n : ℕ} (hs : IsSquare n) (ho : Odd n)
    (he : 1 + σ 1 n = 2 * n) : σ 1 n % 16 = 1 := by
  obtain ⟨r, hr⟩ := hs
  have hro : Odd r := (Nat.odd_mul.mp (hr ▸ ho)).1
  have hodd := Nat.odd_iff.mp hro
  have hmod : n % 8 = 1 := by
    rw [hr, Nat.mul_mod]
    have hcases : r % 8 = 1 ∨ r % 8 = 3 ∨ r % 8 = 5 ∨ r % 8 = 7 := by omega
    rcases hcases with h | h | h | h <;> rw [h] <;> decide
  omega

end OMA.OddAlmost

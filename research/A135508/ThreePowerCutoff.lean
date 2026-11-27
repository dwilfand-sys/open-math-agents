import A135508EventualDivisibility

namespace A135508Progress

open OeisA135508
open OMA.R_OeisA135508_conjecture_R1
open OMA.R_OeisA135508_conjecture_R1_H2_R1

private theorem triple_step {t : ℕ} (ht : 2 ≤ t) (hd : t ∣ x (t - 1)) :
    x t = x (t - 1) * 3 := by
  have h := x_succ_fact (t - 1) (by omega)
  rwa [show t - 1 + 1 = t by omega, Nat.gcd_eq_right hd, Nat.div_self (by omega : 0 < t)] at h

private theorem quadruple_step {q : ℕ} (hq : 0 < q) (hd : q ∣ x (2 * q - 1))
    (hmiss : ¬ 2 * q ∣ x (2 * q - 1)) : x (2 * q) = x (2 * q - 1) * 4 := by
  let z := x (2 * q - 1)
  obtain ⟨u, hu⟩ : q ∣ z := hd
  have odd : ¬ 2 ∣ u := by
    rintro ⟨k, hk⟩
    apply hmiss
    use k
    change z = 2 * q * k
    rw [hu, hk]
    ring
  have hg : z.gcd (2 * q) = q := by
    rw [hu, Nat.mul_comm 2 q, Nat.gcd_mul_left,
      (Nat.prime_two.coprime_iff_not_dvd.mpr odd).symm.gcd_eq_one, Nat.mul_one]
  have h := x_succ_fact (2 * q - 1) (by omega)
  rw [show 2 * q - 1 + 1 = 2 * q by omega] at h
  change x (2 * q) = z * (2 + 2 * q / z.gcd (2 * q)) at h
  rwa [hg, Nat.mul_div_cancel 2 hq] at h

/-- Successive pairs of powers of two force at least one additional factor of three. -/
theorem three_pow_explicit (e : ℕ) : 3 ^ e ∣ x (4 ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    let q : ℕ := 4 ^ e
    have qp : 0 < q := by dsimp [q]; positivity
    have hq : q ∣ x q := by
      have eq : q = 2 ^ (2 * e) := by dsimp [q]; rw [pow_mul] <;> norm_num
      rw [eq]
      exact two_pow_hits _
    have prev : q ∣ x (2 * q - 1) := divides_later qp (by omega) hq
    have hthree : 3 ^ e ∣ x q := ih
    rw [show (4 : ℕ)^(e + 1) = 4 * q by exact pow_succ' 4 e, pow_succ]
    by_cases hfull : 2 * q ∣ x (2 * q - 1)
    · have hprev : 3 ^ e ∣ x (2 * q - 1) := divides_later qp (by omega) hthree
      have mid : 3 ^ e * 3 ∣ x (2 * q) := by
        rw [triple_step (t := 2 * q) (by omega) hfull]
        exact Nat.mul_dvd_mul_right hprev 3
      exact divides_later (by omega : 1 ≤ 2 * q) (by omega) mid
    · have mid : 4 * q ∣ x (2 * q) := by
        have equation := quadruple_step qp prev hfull
        obtain ⟨u, hu⟩ := prev
        refine ⟨u, ?_⟩
        rw [equation, hu]
        ring
      have full : 4 * q ∣ x (4 * q - 1) := divides_later (by omega : 1 ≤ 2 * q) (by omega) mid
      have hprev : 3 ^ e ∣ x (4 * q - 1) := divides_later qp (by omega) hthree
      rw [triple_step (t := 4 * q) (by omega) full]
      exact Nat.mul_dvd_mul_right hprev 3

/-- A simultaneous explicit threshold for all divisors supported on 2 and 3. -/
theorem smooth_cutoff (a b n : ℕ) (h₂ : 2 ^ a ≤ n) (h₃ : 4 ^ b ≤ n) :
    (2 ^ a) * (3 ^ b) ∣ x n := by
  have cop := ((by decide : Nat.Coprime 2 3).pow_left a).pow_right b
  exact cop.mul_dvd_of_dvd_of_dvd
    (divides_later (by positivity) h₂ (two_pow_hits a))
    (divides_later (by positivity) h₃ (three_pow_explicit b))

end A135508Progress

import OMAReductions.R_OeisA135508_conjecture_R1_H2_R1
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib

/-!
Eventual divisibility for OEIS A135508. The sequence and its conjecture are due to the OEIS contributors and Bill McEachen. The reductions by @harshshah1618 and @Hennyrick (PR #1354) supply the recurrence identities and persistence lemma used below. The argument combines Dirichlet primes, powers of two, and the index t = x(m). Benoît Cloitre's Primes in LCM recurrences, arXiv:2510.18891v3, Proposition 6.5, gives a stronger description of the 2-adic valuations.
-/

namespace A135508Progress

open OeisA135508
open OMA.R_OeisA135508_conjecture_R1
open OMA.R_OeisA135508_conjecture_R1_H2_R1

/-- Every fixed modulus prime to six divides every sufficiently late recurrence term. -/
theorem eventually_dvd_of_coprime_six (m : ℕ) (hm : m.Coprime 6) :
    ∃ R : ℕ, ∀ n ≥ R, m ∣ x n := by
  by_cases one : m = 1
  · subst m
    exact ⟨0, fun _ _ => one_dvd _⟩
  have nonzero : m ≠ 0 := by
    rintro rfl
    exact (by decide : ¬ Nat.Coprime 0 6) hm
  have m2 : 2 ≤ m := by omega
  have cop2 : m.Coprime 2 := hm.coprime_dvd_right (by decide : 2 ∣ 6)
  have cop3 : Nat.Coprime 3 m := (hm.coprime_dvd_right (by decide : 3 ∣ 6)).symm
  have complement : (m - 2).Coprime m := by
    let d := (m - 2).gcd m
    have first : d ∣ m - 2 := Nat.gcd_dvd_left _ _
    have second : d ∣ m := Nat.gcd_dvd_right _ _
    have twice : d ∣ 2 := by
      have h := Nat.dvd_sub second first
      rwa [show m - (m - 2) = 2 by omega] at h
    change d = 1
    apply Nat.dvd_one.mp
    rw [← cop2.gcd_eq_one]
    exact Nat.dvd_gcd second twice
  let t := Nat.chineseRemainder cop3 2 (m - 2)
  have tc3 : t.val.Coprime 3 :=
    t.property.1.gcd_eq.trans (by decide : Nat.gcd 2 3 = 1)
  have tcm : t.val.Coprime m := t.property.2.gcd_eq.trans complement.gcd_eq_one
  obtain ⟨r, hr5, hr, hrmod⟩ := Nat.forall_exists_prime_gt_and_modEq 5
    (q := 3 * m) (a := t.val) (Nat.mul_ne_zero (by decide) nonzero)
    (Nat.coprime_mul_iff_right.mpr ⟨tc3, tcm⟩)
  have r3 : r % 3 = 2 :=
    (hrmod.of_dvd (show 3 ∣ 3 * m from ⟨m, rfl⟩)).trans t.property.1
  have rsub : r ≡ m - 2 [MOD m] :=
    (hrmod.of_dvd (show m ∣ 3 * m from ⟨3, Nat.mul_comm _ _⟩)).trans t.property.2
  have req := rsub.add_right 2
  rw [Nat.sub_add_cancel m2] at req
  have rplus : m ∣ r + 2 := Nat.modEq_zero_iff_dvd.mp
    (req.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  exact ⟨r, fun _ hn => witness_divides_later hr hr5 r3 rplus hn⟩

/-- McEachen’s equality on every sufficiently late prime in the progression 2 modulo m. -/
theorem eventually_good_for_divisor (m : ℕ) (hm : m.Coprime 6) (hm1 : 1 < m) :
    ∃ N : ℕ, ∀ p ≥ N, p.Prime → m ∣ p - 2 → a (p - 1) = p := by
  obtain ⟨R, hR⟩ := eventually_dvd_of_coprime_six m hm
  refine ⟨R + 5, ?_⟩
  intro p hp hp' hdiv
  rw [prime_target_iff hp' (by omega)]
  intro bad
  have he : p - 3 + 1 = p - 2 := by omega
  have factor : a (p - 3) * Nat.gcd (x (p - 3)) ((p - 3) + 1) = (p - 3) + 1 := by
    rw [a_eq_div_gcd _ (by omega)]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  rw [he, bad] at factor
  have g : Nat.gcd (x (p - 3)) (p - 2) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p - 2)
    simpa only [Nat.mul_one] using factor
  have := Nat.dvd_gcd (hR (p - 3) (by omega)) hdiv
  rw [g, Nat.dvd_one] at this
  omega

end A135508Progress

namespace A135508Progress

open OeisA135508
open OMA.R_OeisA135508_conjecture_R1
open OMA.R_OeisA135508_conjecture_R1_H2_R1

private lemma recurrence_add (k : ℕ) (hk : 1 ≤ k) :
    x (k + 1) = 2 * x k + Nat.lcm (x k) (k + 1) := by
  cases k with
  | zero => omega
  | succ j => rfl

/-- At its own index, each power of two already divides the sequence. -/
theorem two_pow_hits (e : ℕ) : 2 ^ e ∣ x (2 ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    let t : ℕ := 2 ^ (e + 1)
    have hm : 0 < (2 : ℕ) ^ e := by positivity
    have he : t = 2 * 2 ^ e := by dsimp [t]; rw [pow_succ']
    have ht : 2 ≤ t := by omega
    have prev : 2 ^ e ∣ x (t - 1) := divides_later hm (by omega) ih
    have dterm : t ∣ 2 * x (t - 1) := by
      conv_lhs => rw [he]
      exact Nat.mul_dvd_mul_left 2 prev
    have h := recurrence_add (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at h
    change t ∣ x t
    rw [h]
    exact dvd_add dterm (Nat.dvd_lcm_right _ _)

private theorem growth {m : ℕ} (hm : 2 ≤ m) : m + 1 < x m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [recurrence_add k (by omega)]; omega

/-- Taking the future index t = x(m) makes the multiplier at t exactly three. -/
theorem three_pow_hits (e : ℕ) : ∃ m : ℕ, 2 ≤ m ∧ 3 ^ e ∣ x m := by
  induction e with
  | zero => exact ⟨2, by decide, by simp⟩
  | succ e ih =>
    obtain ⟨m, hm, hd⟩ := ih
    let t := x m
    have ht : m + 1 < t := growth hm
    have dt : t ∣ x (t - 1) := divides_later (by omega : 1 ≤ m) (by omega) (dvd_refl (x m))
    have hprev : 3 ^ e ∣ x (t - 1) := divides_later (by omega : 1 ≤ m) (by omega) hd
    have hf := x_succ_fact (t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega, Nat.gcd_eq_right dt, Nat.div_self (by omega : 0 < t)] at hf
    refine ⟨t, by omega, ?_⟩
    rw [hf, pow_succ]
    exact Nat.mul_dvd_mul_right hprev 3

theorem eventually_two_pow (e : ℕ) : ∃ R : ℕ, ∀ n ≥ R, 2 ^ e ∣ x n := by
  exact ⟨2 ^ e, fun _ hn => divides_later (by positivity) hn (two_pow_hits e)⟩

theorem eventually_three_pow (e : ℕ) : ∃ R : ℕ, ∀ n ≥ R, 3 ^ e ∣ x n := by
  obtain ⟨R, hR, hd⟩ := three_pow_hits e
  exact ⟨R, fun _ hn => divides_later (by omega) hn hd⟩

end A135508Progress

namespace A135508Progress

open OeisA135508

/-- Every fixed positive modulus eventually divides every term of A135508's auxiliary sequence. -/
theorem eventually_dvd (m : ℕ) (hm : 0 < m) : ∃ R : ℕ, ∀ n ≥ R, m ∣ x n := by
  revert hm
  induction m using Nat.recOnPrimeCoprime with
  | zero => intro h; omega
  | prime_pow p e hp =>
    intro _
    by_cases two : p = 2
    · subst p
      exact eventually_two_pow e
    by_cases three : p = 3
    · subst p
      exact eventually_three_pow e
    have cop : p.Coprime 6 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro h
      obtain h₂ | h₃ := hp.dvd_mul.mp (show p ∣ 2 * 3 from h)
      · exact two ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h₂)
      · exact three ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h₃)
    exact eventually_dvd_of_coprime_six _ (cop.pow_left e)
  | coprime a b ha hb hc iha ihb =>
    intro _
    obtain ⟨A, hA⟩ := iha (by omega)
    obtain ⟨B, hB⟩ := ihb (by omega)
    exact ⟨max A B, fun n hn => hc.mul_dvd_of_dvd_of_dvd
      (hA n ((le_max_left _ _).trans hn)) (hB n ((le_max_right _ _).trans hn))⟩

end A135508Progress

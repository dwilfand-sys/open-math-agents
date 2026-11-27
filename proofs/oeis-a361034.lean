import OMAStatements.S_oeis_a361034
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-! Parity of the factorial quotient of OEIS A361034.
Peter Bala posed the conjecture. @LAPRAI formalized its statement.
Shifted multinomial coefficients certify divisibility after doubling, and
the binary factorial valuation both removes that factor and determines parity.
Source: https://oeis.org/A361034
Credit: @dwilfand-sys
-/

private lemma shifted_four {n s : ℕ} (a b c d i j k l : ℕ)
    (hs : a+b+c+d=4*n) (hi : a+i=n) (hj : b+j=n+s) (hk : c+k=n+s) (hl : d+l=n+s) :
    ∃ w : ℤ, ((4*n).factorial : ℤ) * ((a+1).ascFactorial i : ℤ) *
      ((b+1).ascFactorial j : ℤ) * ((c+1).ascFactorial k : ℤ) *
      ((d+1).ascFactorial l : ℤ) =
      (n.factorial : ℤ) * ((n+s).factorial : ℤ)^3 * w := by
  have h₁ := Nat.factorial_mul_factorial_dvd_factorial_add a b
  have h₂ := Nat.factorial_mul_factorial_dvd_factorial_add (a+b) c
  have h₃ := Nat.factorial_mul_factorial_dvd_factorial_add (a+b+c) d
  have habc := (Nat.mul_dvd_mul_right h₁ c.factorial).trans h₂
  obtain ⟨w, hw⟩ := (Nat.mul_dvd_mul_right habc d.factorial).trans h₃
  have fa := Nat.factorial_mul_ascFactorial a i
  have fb := Nat.factorial_mul_ascFactorial b j
  have fc := Nat.factorial_mul_ascFactorial c k
  have fd := Nat.factorial_mul_ascFactorial d l
  rw [hi] at fa
  rw [hj] at fb
  rw [hk] at fc
  rw [hl] at fd
  refine ⟨w, ?_⟩
  have eqn : (4*n).factorial * (a+1).ascFactorial i * (b+1).ascFactorial j *
      (c+1).ascFactorial k * (d+1).ascFactorial l = n.factorial * (n+s).factorial^3 * w := by
    calc
      _ = (a.factorial * (a+1).ascFactorial i) * (b.factorial * (b+1).ascFactorial j) *
          (c.factorial * (c+1).ascFactorial k) * (d.factorial * (d+1).ascFactorial l) * w := by
        rw [← hs, hw]
        ring
      _ = _ := by rw [fa, fb, fc, fd]; ring
  exact_mod_cast eqn

private lemma twice_numerator_dvd_shift2 (n : ℕ) :
    n.factorial * (n+2).factorial^3 ∣ 5040 * (4*n).factorial := by
  by_cases hsmall : n < 6
  · interval_cases n <;> decide +kernel
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = t+6 := ⟨n-6, by omega⟩
  obtain ⟨w1, h1⟩ := shifted_four (n := t+6) (s := 2)
    (t+6) (t+8) (t+5) (t+5) 0 0 3 3 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨w2, h2⟩ := shifted_four (n := t+6) (s := 2)
    (t+6) (t+7) (t+7) (t+4) 0 1 1 4 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨w3, h3⟩ := shifted_four (n := t+6) (s := 2)
    (t+6) (t+7) (t+6) (t+5) 0 1 2 3 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨w4, h4⟩ := shifted_four (n := t+6) (s := 2)
    (t+6) (t+6) (t+6) (t+6) 0 2 2 2 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨w5, h5⟩ := shifted_four (n := t+6) (s := 2)
    (t+4) (t+8) (t+8) (t+4) 2 0 0 4 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨w6, h6⟩ := shifted_four (n := t+6) (s := 2)
    (t+2) (t+8) (t+7) (t+7) 4 0 1 1 (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨w7, h7⟩ := shifted_four (n := t+6) (s := 2)
    t (t+8) (t+8) (t+8) 6 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hz : ((t+6).factorial : ℤ) * (((t+6)+2).factorial : ℤ)^3 ∣
      5040 * ((4*(t+6)).factorial : ℤ) := by
    refine ⟨-1324 * w1 + 1508 * w2 - 772 * w3 + 630 * w4 - 223 * w5 + 180 * w6 + w7, ?_⟩
    simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat] at h1 h2 h3 h4 h5 h6 h7
    linear_combination -1324 * h1 + 1508 * h2 - 772 * h3 + 630 * h4 - 223 * h5 + 180 * h6 + h7
  exact_mod_cast hz

namespace OMA.FactorialQuotient

private abbrev v (n : ℕ) := n.factorial.factorization 2

private theorem v_double (n : ℕ) : v (2 * n) = v n + n :=
  Nat.factorization_factorial_mul Nat.prime_two

private theorem v_double_add_one (n : ℕ) : v (2 * n + 1) = v n + n := by
  change ((2 * n + 1).factorial).factorization 2 = _
  rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero _),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by omega : ¬2 ∣ 2 * n + 1),
    zero_add]
  exact v_double n

/-- Among the positive lengths, `n!` contains exactly `n−1` twos at powers of two. -/
theorem binary_factorial (n : ℕ) (hn : 0 < n) :
    n.factorial.factorization 2 < n ∧
      (n.factorial.factorization 2 + 1 = n ↔ ∃ k : ℕ, n = 2 ^ k) := by
  change v n < n ∧ (v n + 1 = n ↔ _)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n = 1
    · subst n
      constructor
      · simp [v]
      · constructor
        · intro _
          exact ⟨0, by simp⟩
        · intro _
          simp [v]
    let m := n / 2
    have hm : 0 < m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    obtain ⟨bound, powers⟩ := ih m hmn hm
    have cases' : n = 2 * m ∨ n = 2 * m + 1 := by dsimp [m]; omega
    rcases cases' with even | odd
    · rw [even, v_double]
      constructor
      · omega
      · constructor
        · intro eq
          obtain ⟨k, hk⟩ := powers.mp (by omega)
          exact ⟨k + 1, by rw [hk, pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk; omega
          | succ k =>
            rw [pow_succ] at hk
            have eq := powers.mpr ⟨k, by omega⟩
            omega
    · rw [odd, v_double_add_one]
      constructor
      · omega
      · constructor
        · intro eq
          omega
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk; omega
          | succ k => rw [pow_succ] at hk; omega

theorem binary_balance (n shift c : ℕ) (hs : 0 < shift) (hc : c ≠ 0)
    (hv : c.factorization 2 + 3 = 3 * shift) :
    let num := c * (4 * n).factorial
    let den := n.factorial * (n + shift).factorial ^ 3
    den.factorization 2 ≤ num.factorization 2 ∧
      (den.factorization 2 = num.factorization 2 ↔ ∃ k : ℕ, n + shift = 2 ^ k) := by
  dsimp only
  obtain ⟨bound, powers⟩ := binary_factorial (n + shift) (by omega)
  have hfour : v (4 * n) = v n + 3 * n := by
    have h : 4 * n = 2 * (2 * n) := by omega
    rw [h, v_double, v_double]
    omega
  rw [Nat.factorization_mul hc (Nat.factorial_ne_zero _),
    Nat.factorization_mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
    Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
  change (4 * n).factorial.factorization 2 = n.factorial.factorization 2 + 3 * n at hfour
  constructor
  · omega
  · rw [← powers]
    omega

/-- Remove the auxiliary factor two, then read the parity of the exact quotient. -/
theorem odd_exact_quotient (d a : ℕ) (hd : d ≠ 0) (ha : a ≠ 0)
    (h : d ∣ 2 * a) (h₂ : d.factorization 2 ≤ a.factorization 2) :
    d ∣ a ∧ (Odd (a / d) ↔ d.factorization 2 = a.factorization 2) := by
  have hda : d ∣ a := by
    apply (Nat.factorization_le_iff_dvd hd ha).mp
    have htotal := (Nat.factorization_le_iff_dvd hd (mul_ne_zero (by decide) ha)).mpr h
    intro p
    by_cases same : p = 2
    · simpa [same] using h₂
    · have hrest := htotal p
      rw [Nat.factorization_mul (by decide : 2 ≠ 0) ha, Finsupp.add_apply,
        Nat.prime_two.factorization] at hrest
      simpa [Finsupp.single_apply, same, Ne.symm same] using hrest
  refine ⟨hda, ?_⟩
  have hprod : a / d * d = a := Nat.div_mul_cancel hda
  have hq : a / d ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at hprod
    exact ha hprod.symm
  have sum : (a / d).factorization 2 + d.factorization 2 = a.factorization 2 := by
    calc
      _ = (a / d * d).factorization 2 := by rw [Nat.factorization_mul hq hd, Finsupp.add_apply]
      _ = _ := by rw [hprod]
  have odd_iff : Odd (a / d) ↔ ¬ 2 ∣ a / d := by rw [Nat.odd_iff]; omega
  rw [odd_iff, ← show (a / d).factorization 2 = 0 ↔ ¬ 2 ∣ a / d by
    simp [Nat.factorization_eq_zero_iff, Nat.prime_two, hq]]
  omega

end OMA.FactorialQuotient

open OMA.FactorialQuotient OMA.S_oeis_a361034

theorem OMA.solution : type_of% @OMA.S_oeis_a361034.main := by
  intro n
  let d := n.factorial * (n + 2).factorial ^ 3
  let u := 2520 * (4 * n).factorial
  have hd : d ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hu : u ≠ 0 := mul_ne_zero (by decide) (Nat.factorial_ne_zero _)
  have h2 : d ∣ 2 * u := by
    simpa only [d, u, ← Nat.mul_assoc] using twice_numerator_dvd_shift2 n
  have constantVal : (2520 : ℕ).factorization 2 + 3 = 3 * 2 := by
    have h : (2520 : ℕ) = 2 ^ 3 * 315 := by decide
    rw [h, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)] <;> decide
  obtain ⟨le, characterization⟩ := binary_balance n 2 2520 (by decide) (by decide) constantVal
  change Odd (u / d) ↔ _
  rw [(odd_exact_quotient d u hd hu h2 le).2, characterization]
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp only [pow_zero] at hk; omega
    | succ k => exact ⟨k + 1, by omega, by omega⟩
  · rintro ⟨k, hk, hn⟩
    cases k with
    | zero => omega
    | succ k =>
      have pos : 0 < 2 ^ k := by positivity
      rw [pow_succ] at hn
      exact ⟨k + 1, by simpa only [pow_succ] using (show n + 2 = 2 ^ k * 2 by omega)⟩

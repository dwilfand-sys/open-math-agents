import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-! A uniform integrality and parity result for the factorial array of Peter Bala.
The entries with shifts 1, 2, 3 give OEIS A361033, A361034 and A361035.
An earlier independent Lean proof of the last two rows was merged at
https://github.com/the-omega-institute/trureturing/pull/22639 (ElonSG, 2026).
Sources: https://oeis.org/A361032 and https://oeis.org/A361035.
-/

/-- Legendre summand for `(4a)! (4b)! / (a! b! ((a+b)!)³)`. -/
theorem quarter_floor (a b q : ℕ) (hq : 0 < q) :
    (a + b) / q * 3 + a / q + b / q ≤ (4 * a) / q + (4 * b) / q := by
  have scale (x : ℕ) : 4 * (x / q) ≤ (4 * x) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      (4 * (x / q)) * q = 4 * (x / q * q) := Nat.mul_assoc _ _ _
      _ ≤ 4 * x := Nat.mul_le_mul_left 4 (Nat.div_mul_le_self x q)
  by_cases carry : (a + b) / q ≤ a / q + b / q
  · have ha := scale a
    have hb := scale b
    omega
  · have upper (x : ℕ) : x < (x / q + 1) * q :=
      (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
    have four : 4 * ((a + b) / q) ≤ (4 * a) / q + (4 * b) / q + 1 := by
      by_contra! fail
      have reverse : ((4*a)/q + (4*b)/q + 2) * q ≤ (4*((a+b)/q)) * q :=
        Nat.mul_le_mul_right q (by omega)
      have base := Nat.mul_le_mul_left 4 (Nat.div_mul_le_self (a + b) q)
      have ua := upper (4 * a)
      have ub := upper (4 * b)
      nlinarith only [reverse, base, ua, ub]
    omega

/-- A symmetric factorial ratio is integral for every pair of nonnegative shifts. -/
theorem factorial_pair_divisibility (n s : ℕ) :
    n.factorial * s.factorial * (n + s).factorial ^ 3 ∣
      (4 * n).factorial * (4 * s).factorial := by
  have hns := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s)
  have hcube := pow_ne_zero 3 (Nat.factorial_ne_zero (n + s))
  apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero hns hcube)
    (mul_ne_zero (Nat.factorial_ne_zero (4 * n)) (Nat.factorial_ne_zero (4 * s)))).mp
  intro p hp
  let bound := 4 * (n + s) + 1
  have expand (j : ℕ) (hj : j < bound) :
      j.factorial.factorization p = ∑ i ∈ Finset.Ico 1 bound, j / p ^ i :=
    Nat.factorization_factorial hp ((Nat.log_le_self p j).trans_lt hj)
  have mulVal (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a * b).factorization p = a.factorization p + b.factorization p := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have cubeVal (a : ℕ) (ha : a ≠ 0) :
      (a ^ 3).factorization p = 3 * a.factorization p := by
    rw [show a ^ 3 = a * a * a by ring, mulVal _ _ (mul_ne_zero ha ha) ha, mulVal _ _ ha ha]
    omega
  rw [mulVal _ _ hns hcube, mulVal _ _ (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s),
    cubeVal _ (Nat.factorial_ne_zero (n + s)),
    mulVal _ _ (Nat.factorial_ne_zero (4 * n)) (Nat.factorial_ne_zero (4 * s))]
  rw [expand n (by dsimp [bound]; omega), expand s (by dsimp [bound]; omega),
    expand (n + s) (by dsimp [bound]; omega), expand (4 * n) (by dsimp [bound]; omega),
    expand (4 * s) (by dsimp [bound]; omega)]
  have h : (∑ i ∈ Finset.Ico 1 bound,
      ((n + s) / (p ^ i) * 3 + n / (p ^ i) + s / (p ^ i))) ≤
      ∑ i ∈ Finset.Ico 1 bound, ((4 * n) / (p ^ i) + (4 * s) / (p ^ i)) :=
    Finset.sum_le_sum (fun i _ ↦ quarter_floor n s (p ^ i) (pow_pos hp.pos i))
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at h
  omega

/-- Cancel the constant factorial on the two sides. -/
theorem factorial_shift_divisibility (n s C : ℕ) (hC : (4 * s).factorial = s.factorial * C) :
    n.factorial * (n + s).factorial ^ 3 ∣ C * (4 * n).factorial := by
  obtain ⟨t, ht⟩ := factorial_pair_divisibility n s
  refine ⟨t, mul_left_cancel₀ (Nat.factorial_ne_zero s) ?_⟩
  calc
    s.factorial * (C * (4 * n).factorial) = (4 * n).factorial * (4 * s).factorial := by
      rw [hC]
      ring
    _ = (n.factorial * s.factorial * (n + s).factorial ^ 3) * t := ht
    _ = s.factorial * ((n.factorial * (n + s).factorial ^ 3) * t) := by ring

namespace FactorialQuotient

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

end FactorialQuotient

/-- A power of two in the numerator can be cancelled once the valuation at two is known. -/
theorem remove_twos (d u k : ℕ) (hd : d ≠ 0) (hu : u ≠ 0)
    (h : d ∣ 2 ^ k * u) (hle : d.factorization 2 ≤ u.factorization 2) : d ∣ u := by
  apply (Nat.factorization_prime_le_iff_dvd hd hu).mp
  intro p hp
  by_cases p2 : p = 2
  · simpa only [p2] using hle
  · have hpow : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
    have h' := (Nat.factorization_prime_le_iff_dvd hd (mul_ne_zero hpow hu)).mpr h p hp
    rw [Nat.factorization_mul hpow hu, Finsupp.add_apply, Nat.prime_two.factorization_pow] at h'
    simpa [Finsupp.single_apply, Ne.symm p2] using h'

open FactorialQuotient

/-- For every positive shift, the normalized factorial quotient is an integer.
Its odd terms occur exactly when the shifted index is a power of two. -/
theorem all_shift_parities (n s c : ℕ) (hs : 0 < s)
    (constant : (4 * s).factorial = s.factorial * (8 * c)) :
    let d := n.factorial * (n + s).factorial ^ 3
    let u := c * (4 * n).factorial
    d ∣ u ∧ (Odd (u / d) ↔ ∃ k : ℕ, n + s = 2 ^ k) := by
  let d := n.factorial * (n + s).factorial ^ 3
  let u := c * (4 * n).factorial
  change d ∣ u ∧ (Odd (u / d) ↔ _)
  have hc : c ≠ 0 := by
    intro hz
    rw [hz, mul_zero, mul_zero] at constant
    exact Nat.factorial_ne_zero _ constant
  have hd : d ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hu : u ≠ 0 := mul_ne_zero hc (Nat.factorial_ne_zero _)
  have val : c.factorization 2 + 3 = 3 * s := by
    have four : (4 * s).factorial.factorization 2 = s.factorial.factorization 2 + 3 * s := by
      rw [show 4 * s = 2 * (2 * s) by omega,
        Nat.factorization_factorial_mul Nat.prime_two, Nat.factorization_factorial_mul Nat.prime_two]
      omega
    have eight : (8 : ℕ).factorization 2 = 3 := by
      change ((2 : ℕ) ^ 3).factorization 2 = 3
      rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
    rw [constant, Nat.factorization_mul (Nat.factorial_ne_zero _) (mul_ne_zero (by decide) hc),
      Finsupp.add_apply, Nat.factorization_mul (by decide : (8 : ℕ) ≠ 0) hc,
      Finsupp.add_apply, eight] at four
    omega
  obtain ⟨hle, hpow⟩ := binary_balance n s c hs hc val
  have eightDiv : d ∣ 2 ^ 3 * u := by
    have h := factorial_shift_divisibility n s (8 * c) constant
    simpa only [u, d, Nat.mul_assoc] using h
  have integral := remove_twos d u 3 hd hu eightDiv hle
  have twice : d ∣ 2 * u := integral.trans ⟨2, Nat.mul_comm _ _⟩
  exact ⟨integral, (odd_exact_quotient d u hd hu twice hle).2.trans hpow⟩

/-- The normalizing factor is integral at every positive shift. -/
theorem shift_constant_exact (s : ℕ) (hs : 0 < s) :
    (4 * s).factorial = s.factorial * (8 * ((4*s).factorial / (8 * s.factorial))) := by
  have base := Nat.factorial_dvd_factorial (show s ≤ 4*s by omega)
  have scaled : 8 * s.factorial ∣ (2:ℕ)^3 * (4*s).factorial := by
    obtain ⟨t, ht⟩ := base
    refine ⟨t, ?_⟩
    rw [ht]
    ring
  have eight : (8 : ℕ).factorization 2 = 3 := by
    change ((2 : ℕ) ^ 3).factorization 2 = 3
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  have four : (4 * s).factorial.factorization 2 = s.factorial.factorization 2 + 3*s := by
    rw [show 4 * s = 2 * (2 * s) by omega,
      Nat.factorization_factorial_mul Nat.prime_two, Nat.factorization_factorial_mul Nat.prime_two]
    omega
  have balance : (8 * s.factorial).factorization 2 ≤ (4 * s).factorial.factorization 2 := by
    rw [four, Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _), Finsupp.add_apply, eight]
    omega
  have exactDiv := remove_twos _ _ 3 (mul_ne_zero (by decide) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _) scaled balance
  calc
    (4*s).factorial = (4*s).factorial / (8*s.factorial) * (8*s.factorial) :=
      (Nat.div_mul_cancel exactDiv).symm
    _ = _ := by ring

/-- A single formula specializes to the parity conjectures A361033, A361034, and A361035. -/
theorem all_positive_shifts (n s : ℕ) (hs : 0 < s) :
    let c := (4 * s).factorial / (8 * s.factorial)
    let d := n.factorial * (n + s).factorial ^ 3
    let u := c * (4 * n).factorial
    d ∣ u ∧ (Odd (u / d) ↔ ∃ k : ℕ, n + s = 2 ^ k) :=
  all_shift_parities n s _ hs (shift_constant_exact s hs)

/-- The exact two-adic valuation is three times the number of ones in the
binary expansion of the sum of the two indices, including at `(0, 0)`. -/
theorem factorial_pair_valuation (n s : ℕ) :
    (((4 * n).factorial * (4 * s).factorial) /
      (n.factorial * s.factorial * (n + s).factorial ^ 3)).factorization 2 =
      3 * ((2 : ℕ).digits (n + s)).sum := by
  let d := n.factorial * s.factorial * (n + s).factorial ^ 3
  let u := (4 * n).factorial * (4 * s).factorial
  let q := u / d
  have hns := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s)
  have hcube := pow_ne_zero 3 (Nat.factorial_ne_zero (n + s))
  have hd : d ≠ 0 := mul_ne_zero hns hcube
  have hu : u ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have heq : q * d = u := Nat.div_mul_cancel (factorial_pair_divisibility n s)
  have hq : q ≠ 0 := fun zero ↦ hu (by simpa [zero] using heq.symm)
  have mulVal (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a * b).factorization 2 = a.factorization 2 + b.factorization 2 := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have total : q.factorization 2 + d.factorization 2 = u.factorization 2 :=
    (mulVal _ _ hq hd).symm.trans (congrArg (fun j : ℕ ↦ j.factorization 2) heq)
  have vd : d.factorization 2 = n.factorial.factorization 2 + s.factorial.factorization 2 +
      3 * (n + s).factorial.factorization 2 := by
    dsimp only [d]
    rw [mulVal _ _ hns hcube, mulVal _ _ (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s),
      Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul]
  have four (t : ℕ) : (4 * t).factorial.factorization 2 = t.factorial.factorization 2 + 3 * t := by
    rw [show 4 * t = 2 * (2 * t) by omega,
      Nat.factorization_factorial_mul Nat.prime_two, Nat.factorization_factorial_mul Nat.prime_two]
    omega
  have vu : u.factorization 2 = (n.factorial.factorization 2 + 3 * n) +
      (s.factorial.factorization 2 + 3 * s) := by
    dsimp only [u]
    rw [mulVal _ _ (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _), four n, four s]
  have vdigs : (n + s).factorial.factorization 2 = n + s - ((2 : ℕ).digits (n + s)).sum := by
    simpa using (Nat.sub_one_mul_factorization_factorial (n := n + s) Nat.prime_two)
  have bound := Nat.digit_sum_le 2 (n + s)
  change q.factorization 2 = _
  omega

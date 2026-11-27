import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-! Integrality of all rows of Peter Bala's generalized de Bruijn numbers.
The array of OEIS A361027 has shift `s = row + 1`. Its entry in column `n` is
`(3s)! (3n)! / (3 s! n! ((s+n)!)²)`.
Source: https://oeis.org/A361027
-/

namespace GeneralizedDeBruijn

theorem third_floor (a b q : ℕ) (hq : 0 < q) :
    (a + b) / q * 2 + a / q + b / q ≤ (3 * a) / q + (3 * b) / q := by
  have scale (x : ℕ) : 3 * (x / q) ≤ (3 * x) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      (3 * (x / q)) * q = 3 * (x / q * q) := Nat.mul_assoc _ _ _
      _ ≤ 3 * x := Nat.mul_le_mul_left 3 (Nat.div_mul_le_self x q)
  by_cases carry : (a + b) / q ≤ a / q + b / q
  · have ha := scale a
    have hb := scale b
    omega
  · have upper (x : ℕ) : x < (x / q + 1) * q :=
      (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
    have three : 3 * ((a + b) / q) ≤ (3 * a) / q + (3 * b) / q + 1 := by
      by_contra! fail
      have reverse : ((3*a)/q + (3*b)/q + 2) * q ≤ (3*((a+b)/q)) * q :=
        Nat.mul_le_mul_right q (by omega)
      have base := Nat.mul_le_mul_left 3 (Nat.div_mul_le_self (a + b) q)
      have ua := upper (3 * a)
      have ub := upper (3 * b)
      nlinarith only [reverse, base, ua, ub]
    omega

/-- A symmetric factorial ratio is integral for every pair of nonnegative shifts. -/
theorem cubic_pair_divisibility (n s : ℕ) :
    n.factorial * s.factorial * (n + s).factorial ^ 2 ∣
      (3 * n).factorial * (3 * s).factorial := by
  have hns := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s)
  have hsq := pow_ne_zero 2 (Nat.factorial_ne_zero (n + s))
  apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero hns hsq)
    (mul_ne_zero (Nat.factorial_ne_zero (3 * n)) (Nat.factorial_ne_zero (3 * s)))).mp
  intro p hp
  let bound := 3 * (n + s) + 1
  have expand (j : ℕ) (hj : j < bound) :
      j.factorial.factorization p = ∑ i ∈ Finset.Ico 1 bound, j / p ^ i :=
    Nat.factorization_factorial hp ((Nat.log_le_self p j).trans_lt hj)
  have mulVal (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a * b).factorization p = a.factorization p + b.factorization p := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have squareVal (a : ℕ) (ha : a ≠ 0) :
      (a ^ 2).factorization p = 2 * a.factorization p := by
    rw [show a ^ 2 = a * a by ring, mulVal _ _ ha ha]
    omega
  rw [mulVal _ _ hns hsq, mulVal _ _ (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s),
    squareVal _ (Nat.factorial_ne_zero (n + s)),
    mulVal _ _ (Nat.factorial_ne_zero (3 * n)) (Nat.factorial_ne_zero (3 * s))]
  rw [expand n (by dsimp [bound]; omega), expand s (by dsimp [bound]; omega),
    expand (n + s) (by dsimp [bound]; omega), expand (3 * n) (by dsimp [bound]; omega),
    expand (3 * s) (by dsimp [bound]; omega)]
  have h : (∑ i ∈ Finset.Ico 1 bound,
      ((n + s) / (p ^ i) * 2 + n / (p ^ i) + s / (p ^ i))) ≤
      ∑ i ∈ Finset.Ico 1 bound, ((3 * n) / (p ^ i) + (3 * s) / (p ^ i)) :=
    Finset.sum_le_sum (fun i _ ↦ third_floor n s (p ^ i) (pow_pos hp.pos i))
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at h
  omega

theorem cubic_pair_valuation (n s : ℕ) :
    (((3 * n).factorial * (3 * s).factorial) /
      (n.factorial * s.factorial * (n + s).factorial ^ 2)).factorization 3 =
      ((3 : ℕ).digits (n + s)).sum := by
  let d := n.factorial * s.factorial * (n + s).factorial ^ 2
  let u := (3 * n).factorial * (3 * s).factorial
  let q := u / d
  have hns := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s)
  have hsq := pow_ne_zero 2 (Nat.factorial_ne_zero (n + s))
  have hd : d ≠ 0 := mul_ne_zero hns hsq
  have hu : u ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have heq : q * d = u := Nat.div_mul_cancel (cubic_pair_divisibility n s)
  have hq : q ≠ 0 := fun zero ↦ hu (by simpa [zero] using heq.symm)
  have mulVal (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have total : q.factorization 3 + d.factorization 3 = u.factorization 3 :=
    (mulVal _ _ hq hd).symm.trans (congrArg (fun j : ℕ ↦ j.factorization 3) heq)
  have vd : d.factorization 3 = n.factorial.factorization 3 + s.factorial.factorization 3 +
      2 * (n + s).factorial.factorization 3 := by
    dsimp only [d]
    rw [mulVal _ _ hns hsq, mulVal _ _ (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s),
      Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul]
  have three (t : ℕ) : (3 * t).factorial.factorization 3 = t.factorial.factorization 3 + t :=
    Nat.factorization_factorial_mul (by decide : Nat.Prime 3)
  have vu : u.factorization 3 = (n.factorial.factorization 3 + n) +
      (s.factorial.factorization 3 + s) := by
    dsimp only [u]
    rw [mulVal _ _ (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _), three n, three s]
  have vdigs : 2 * (n + s).factorial.factorization 3 = n + s - ((3 : ℕ).digits (n + s)).sum := by
    simpa using (Nat.sub_one_mul_factorization_factorial (n := n + s) (by decide : Nat.Prime 3))
  have bound := Nat.digit_sum_le 3 (n + s)
  change q.factorization 3 = _
  omega

private theorem ternary_digit_sum_ne_zero (j : ℕ) (hj : 0 < j) : ((3 : ℕ).digits j).sum ≠ 0 := by
  have clear (l : List ℕ) : l.sum = 0 → Nat.ofDigits 3 l = 0 := by
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro h
      rw [List.sum_cons] at h
      have ha : a = 0 := by omega
      have hl : l.sum = 0 := by omega
      simp [Nat.ofDigits_cons, ha, ih hl]
  intro hz
  have invalid := clear _ hz
  rw [Nat.ofDigits_digits] at invalid
  omega

/-- The additional factor of three divides at every positive total degree. -/
theorem normalized_cubic_pair (n s : ℕ) (hpos : 0 < n + s) :
    3 * (n.factorial * s.factorial * (n + s).factorial ^ 2) ∣
      (3 * n).factorial * (3 * s).factorial := by
  let d := n.factorial * s.factorial * (n + s).factorial ^ 2
  let u := (3 * n).factorial * (3 * s).factorial
  have eq : u / d * d = u := Nat.div_mul_cancel (cubic_pair_divisibility n s)
  have val : (u / d).factorization 3 ≠ 0 := by
    rw [show (u / d).factorization 3 = ((3 : ℕ).digits (n + s)).sum from cubic_pair_valuation n s]
    exact ternary_digit_sum_ne_zero _ hpos
  obtain ⟨t, ht⟩ := Nat.dvd_of_factorization_pos val
  refine ⟨t, eq.symm.trans ?_⟩
  change (u / d) * d = (3 * d) * t
  rw [ht]
  ring

/-- The row-dependent multiplier used by Bala is integral at every shift. -/
theorem cubic_coefficient_exact (s : ℕ) (hs : 0 < s) :
    ((3 * s).factorial / (3 * s.factorial)) * (3 * s.factorial) = (3 * s).factorial := by
  apply Nat.div_mul_cancel
  have h : 3 * (s.factorial * s.factorial ^ 2) ∣ (3 * s).factorial := by
    simpa only [Nat.mul_zero, Nat.factorial_zero, one_mul, zero_add] using
      (normalized_cubic_pair 0 s (by omega))
  obtain ⟨t, ht⟩ := h
  exact ⟨s.factorial ^ 2 * t, by rw [ht]; ring⟩

/-- Every entry of the OEIS A361027 square array has exact natural division. -/
theorem all_rows (row n : ℕ) :
    n.factorial * (n + (row + 1)).factorial ^ 2 ∣
      ((3 * (row + 1)).factorial / (3 * (row + 1).factorial)) * (3 * n).factorial := by
  let s := row + 1
  let c := (3 * s).factorial / (3 * s.factorial)
  have hc : c * (3 * s.factorial) = (3 * s).factorial := cubic_coefficient_exact s (by dsimp [s]; omega)
  obtain ⟨t, ht⟩ := normalized_cubic_pair n s (by dsimp [s]; omega)
  change n.factorial * (n + s).factorial ^ 2 ∣ c * (3 * n).factorial
  refine ⟨t, mul_left_cancel₀ (mul_ne_zero (by decide : (3 : ℕ) ≠ 0) (Nat.factorial_ne_zero s)) ?_⟩
  calc
    (3 * s.factorial) * (c * (3 * n).factorial) = (3 * n).factorial * (c * (3 * s.factorial)) := by ring
    _ = (3 * n).factorial * (3 * s).factorial := by rw [hc]
    _ = (3 * (n.factorial * s.factorial * (n + s).factorial ^ 2)) * t := ht
    _ = (3 * s.factorial) * ((n.factorial * (n + s).factorial ^ 2) * t) := by ring

end GeneralizedDeBruijn

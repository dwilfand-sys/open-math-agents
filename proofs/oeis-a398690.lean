import OMAStatements.S_oeis_a398690

/-! Proof of palindromicity for the Verlinde-number triangle. Credit: @dwilfand-sys. -/


namespace VerlindeReflection

open Finset

noncomputable def weight (N i : ℕ) : ℝ := (-1 : ℝ) ^ i * (N.choose i : ℝ)

noncomputable def topCoeff (n j : ℕ) (P : Polynomial ℝ) : ℝ :=
  ∑ i ∈ range (j + 1), weight (n + 1) i * P.eval ((j : ℝ) - i)

/-- A backwards difference of order strictly above the polynomial degree vanishes. -/
theorem backward_zero (N : ℕ) (P : Polynomial ℝ) (hP : P.natDegree < N) (x : ℝ) :
    ∑ i ∈ range (N + 1), weight N i * P.eval (x - i) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (x - N)
  rw [fwdDiff_iter_eq_sum_shift] at h
  rw [← sum_range_reflect (fun i => weight N i * P.eval (x - i)) (N + 1)]
  calc
    _ = ∑ i ∈ range (N + 1),
        ((-1 : ℤ) ^ (N - i) * N.choose i) • P.eval (x - N + i • (1 : ℝ)) := by
          apply sum_congr rfl
          intro i hi
          have hle : i ≤ N := by simpa using mem_range.mp hi
          simp only [Nat.add_sub_cancel, weight, Nat.choose_symm hle, zsmul_eq_mul,
            nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
            Int.cast_natCast, Nat.cast_sub hle]
          rw [show x - ((N : ℝ) - i) = x - N + i by ring]
    _ = 0 := h

theorem reversed_weight (n r : ℕ) (hr : r ≤ n) :
    weight (n + 1) (n + 1 - r) * (-1 : ℝ) ^ n = -weight (n + 1) r := by
  have hsum : n + 1 - r + n = 2 * (n - r) + (r + 1) := by omega
  unfold weight
  rw [Nat.choose_symm (by omega : r ≤ n + 1)]
  calc
    _ = ((-1 : ℝ) ^ (n + 1 - r) * (-1 : ℝ) ^ n) * ((n + 1).choose r : ℝ) := by ring
    _ = _ := by rw [← pow_add, hsum, pow_add, pow_mul, pow_succ]; norm_num <;> ring

/-- Truncating a degree-bounded polynomial sequence against the binomial expansion of
`(1-z)^(n+1)` gives symmetric coefficients if its values reflect about `-1/2`. -/
theorem reflected_numerator (n : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n)
    (href : ∀ x : ℝ, P.eval (-1 - x) = (-1 : ℝ) ^ n * P.eval x)
    (j : ℕ) (hj : j ≤ n) : topCoeff n j P = topCoeff n (n - j) P := by
  let m := n - j
  have hm : m + j = n := by dsimp [m]; omega
  let f := fun i : ℕ => weight (n + 1) i * P.eval ((m : ℝ) - i)
  have hzero : ∑ i ∈ range ((m + 1) + (j + 1)), f i = 0 := by
    rw [show m + 1 + (j + 1) = n + 1 + 1 by omega]
    exact backward_zero (n + 1) P (by omega) m
  rw [sum_range_add] at hzero
  have htail : ∑ i ∈ range (j + 1), f (m + 1 + i) = -topCoeff n j P := by
    rw [← sum_range_reflect (fun i => f (m + 1 + i)) (j + 1)]
    unfold topCoeff
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro r hr
    have hrj : r ≤ j := by simpa using mem_range.mp hr
    have hidx : m + 1 + (j - r) = n + 1 - r := by omega
    simp only [Nat.add_sub_cancel, f]
    rw [show (m : ℝ) - ↑(m + 1 + (j - r)) = -1 - ((j : ℝ) - r) by
      push_cast [Nat.cast_sub hrj]; ring, hidx, href]
    rw [← mul_assoc, reversed_weight n r (by omega), neg_mul]
  rw [htail] at hzero
  change topCoeff n m P + -topCoeff n j P = 0 at hzero
  change topCoeff n j P = topCoeff n m P
  linarith

/-- Every coefficient beyond the degree of the numerator vanishes. -/
theorem reflected_numerator_vanish (n : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n)
    (j : ℕ) (hj : n < j) : topCoeff n j P = 0 := by
  unfold topCoeff
  rw [show j + 1 = (n + 1 + 1) + (j - (n + 1)) by omega, sum_range_add]
  rw [backward_zero (n + 1) P (by omega), zero_add]
  apply sum_eq_zero
  intro i _
  simp [weight, Nat.choose_eq_zero_of_lt (by omega : n + 1 < n + 1 + 1 + i)]

open OMA.S_oeis_a398690

theorem numeratorCoeff_eq_topCoeff (n j : ℕ) (P : Polynomial ℝ)
    (hval : ∀ k : ℕ, rowValue n k = P.eval (k : ℝ)) :
    numeratorCoeff n j = topCoeff n j P := by
  unfold numeratorCoeff topCoeff weight
  apply sum_congr rfl
  intro i hi
  have hij : i ≤ j := by simpa using mem_range.mp hi
  rw [hval, Nat.cast_sub hij]

/-- The original trigonometric question reduces to reflected polynomial interpolation
of its rows. -/
theorem main_of_reflected_rows
    (hint : ∀ n : ℕ, ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧
      (∀ k : ℕ, rowValue n k = P.eval (k : ℝ)) ∧
      ∀ x : ℝ, P.eval (-1 - x) = (-1 : ℝ) ^ n * P.eval x) :
    ∀ n j : ℕ, numeratorCoeff n j = if j ≤ n then numeratorCoeff n (n - j) else 0 := by
  intro n j
  obtain ⟨P, hd, hv, hr⟩ := hint n
  rw [numeratorCoeff_eq_topCoeff n j P hv]
  split_ifs with hj
  · rw [numeratorCoeff_eq_topCoeff n (n - j) P hv]
    exact reflected_numerator n P hd hr j hj
  · exact reflected_numerator_vanish n P hd j (by omega)

end VerlindeReflection


namespace VerlindeNodes

open Finset
open OMA.S_oeis_a398690

noncomputable def angle (k j : ℕ) : ℝ :=
  (2 * (j : ℝ) + 1) * (2 * Real.pi) / (8 * (k : ℝ) + 4)

noncomputable def node (k j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * Real.sin (angle k j)

theorem angle_gt_zero (k j : ℕ) : 0 < angle k j := by
  unfold angle
  positivity

theorem angle_lt_pi (k j : ℕ) (hj : j < 2 * k + 1) : angle k j < Real.pi := by
  have h : j ≤ 2 * k := by omega
  have h' : (j : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast h
  unfold angle
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr h') Real.pi_pos.le]

theorem node_ne_zero (k j : ℕ) (hj : j < 2 * k + 1) : node k j ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Real.sin_pos_of_pos_of_lt_pi (angle_gt_zero k j) (angle_lt_pi k j hj)).ne'

theorem signed_moment_identity (n j : ℕ) (s : ℝ) :
    (-1 : ℝ) ^ ((n + 3) * j) / s ^ (n + 1) = (((-1 : ℝ) ^ j * s)⁻¹) ^ (n + 1) := by
  have he : (n + 3) * j = j * (n + 1) + 2 * j := by ring
  have hsign : (-1 : ℝ) ^ ((n + 3) * j) = (-1 : ℝ) ^ (j * (n + 1)) := by
    rw [he, pow_add, pow_mul (-1 : ℝ) 2 j]
    norm_num
  have hinv : (((-1 : ℝ) ^ j)⁻¹) = (-1 : ℝ) ^ j := by rw [← inv_pow]; norm_num
  rw [hsign, div_eq_mul_inv, mul_inv_rev, hinv, mul_pow, inv_pow, ← pow_mul, mul_comm]

theorem rowValue_eq_moments (n k : ℕ) :
    rowValue n k = (∑ j ∈ range (2 * k + 1), ((node k j)⁻¹) ^ (n + 1)) /
      (2 * (k : ℝ) + 1) := by
  unfold rowValue
  congr 1
  apply sum_congr rfl
  intro j _
  exact signed_moment_identity n j _

noncomputable def complement (k j : ℕ) : ℝ := Real.pi / 2 - angle k j

noncomputable def phase (k j : ℕ) : ℝ := (j : ℝ) * Real.pi - complement k j

theorem node_eq_cos_phase (k j : ℕ) : node k j = Real.cos (phase k j) := by
  rw [phase, Real.cos_nat_mul_pi_sub, complement, Real.cos_pi_div_two_sub, node]

theorem scaled_phase (k j : ℕ) :
    (2 * (k : ℝ) + 1) * phase k j =
      ((j * (k + 1) : ℕ) : ℝ) * (2 * Real.pi) - (k : ℝ) * Real.pi := by
  unfold phase complement angle
  push_cast
  field_simp [show 8 * (k : ℝ) + 4 ≠ 0 by positivity]
  ring

theorem eval_chebyshev_node (k j : ℕ) :
    (Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1)).eval (node k j) = (-1 : ℝ) ^ k := by
  rw [node_eq_cos_phase, Polynomial.Chebyshev.T_real_cos]
  push_cast
  rw [scaled_phase, Real.cos_nat_mul_two_pi_sub, Real.cos_nat_mul_pi]

theorem complement_repr (k j : ℕ) :
    complement k j = ((k : ℝ) - j) * Real.pi / (2 * k + 1) := by
  unfold complement angle
  field_simp [show 8 * (k : ℝ) + 4 ≠ 0 by positivity,
    show 2 * (k : ℝ) + 1 ≠ 0 by positivity]
  ring

theorem sin_phase_ne_zero (k j : ℕ) (hj : j < k) : Real.sin (phase k j) ≠ 0 := by
  have hk : (j : ℝ) < k := by exact_mod_cast hj
  have hpos : 0 < complement k j := by
    rw [complement_repr]
    exact div_pos (mul_pos (sub_pos.mpr hk) Real.pi_pos) (by positivity)
  have hlt : complement k j < Real.pi := by
    rw [complement]
    linarith [angle_gt_zero k j, Real.pi_pos]
  rw [phase, Real.sin_nat_mul_pi_sub]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne')

theorem deriv_chebyshev_node (k j : ℕ) (hj : j < k) :
    (Polynomial.derivative (Polynomial.Chebyshev.T ℝ (2 * (k : ℤ) + 1))).eval (node k j) = 0 := by
  have hu := Polynomial.Chebyshev.U_real_cos (phase k j) (2 * (k : ℤ))
  push_cast at hu
  rw [scaled_phase, Real.sin_nat_mul_two_pi_sub, Real.sin_nat_mul_pi, neg_zero] at hu
  have hu0 := (mul_eq_zero.mp hu).resolve_right (sin_phase_ne_zero k j hj)
  rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul,
    show (2 * (k : ℤ) + 1) - 1 = 2 * (k : ℤ) by ring, node_eq_cos_phase, hu0, mul_zero]

theorem node_mirror (k j : ℕ) (hj : j ≤ k) : node k (2 * k - j) = node k j := by
  have he : 2 * k - j = 2 * (k - j) + j := by omega
  have hs : (-1 : ℝ) ^ (2 * k - j) = (-1 : ℝ) ^ j := by
    rw [he, pow_add, pow_mul]
    norm_num
  have ha : angle k (2 * k - j) = Real.pi - angle k j := by
    unfold angle
    push_cast [Nat.cast_sub (by omega : j ≤ 2 * k)]
    field_simp [show 8 * (k : ℝ) + 4 ≠ 0 by positivity]
    ring
  simp only [node, hs, ha, Real.sin_pi_sub]

theorem node_abs (k j : ℕ) (hj : j ≤ k) :
    |node k j| = Real.sin (angle k j) := by
  have hpos := Real.sin_pos_of_pos_of_lt_pi (angle_gt_zero k j) (angle_lt_pi k j (by omega))
  simp [node, abs_mul, abs_pow, abs_of_pos hpos]

theorem node_abs_strictMono (k : ℕ) : StrictMono (fun j : Fin (k + 1) => |node k j.val|) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  have hik : i.val ≤ k := by have ht := i.isLt; omega
  have hjk : j.val ≤ k := by have ht := j.isLt; omega
  rw [node_abs k _ hik, node_abs k _ hjk]
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  · linarith [angle_gt_zero k i.val, Real.pi_pos]
  · have hjc : 0 ≤ complement k j.val := by
      rw [complement_repr]
      have hr : (j.val : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      exact div_nonneg (mul_nonneg (sub_nonneg.mpr hr) Real.pi_pos.le) (by positivity)
    unfold complement at hjc
    linarith
  · have hr : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij'
    unfold angle
    apply div_lt_div_of_pos_right _ (by positivity)
    exact mul_lt_mul_of_pos_right (by linarith) (by positivity)

theorem node_injective_first_half (k : ℕ) : Function.Injective (fun j : Fin (k + 1) => node k j.val) := by
  intro i j hij
  apply (node_abs_strictMono k).injective
  exact congrArg abs hij

open Polynomial

theorem sq_linear_dvd_of_eval_deriv_eq_zero (P : Polynomial ℝ) (a : ℝ)
    (h0 : P.eval a = 0) (h1 : P.derivative.eval a = 0) : (X - C a)^2 ∣ P := by
  obtain ⟨Q, hq⟩ := dvd_iff_isRoot.mpr (show P.IsRoot a from h0)
  rw [hq] at h1
  have hz : Q.eval a = 0 := by simpa [derivative_mul] using h1
  obtain ⟨S, hs⟩ := dvd_iff_isRoot.mpr (show Q.IsRoot a from hz)
  exact ⟨S, by rw [hq, hs]; ring⟩

noncomputable def shiftedChebyshev (k : ℕ) : Polynomial ℝ :=
  Chebyshev.T ℝ (2 * (k : ℤ) + 1) - C ((-1 : ℝ) ^ k)

theorem characteristic_factors_dvd (k : ℕ) :
    (∏ j ∈ range (k + 1), (X - C (node k j)) ^ (if j = k then 1 else 2 : ℕ)) ∣
      shiftedChebyshev k := by
  classical
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hne : node k i ≠ node k j := by
      intro he
      have eqFin : (⟨i, hi'⟩ : Fin (k + 1)) = ⟨j, hj'⟩ := node_injective_first_half k he
      exact hij (congrArg Fin.val eqFin)
    apply IsCoprime.pow
    apply isCoprime_X_sub_C_of_isUnit_sub
    first | exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)
          | exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne.symm)
  · intro i hi
    have hi' : i ≤ k := by simpa using mem_range.mp hi
    have hz : (shiftedChebyshev k).eval (node k i) = 0 := by
      simp [shiftedChebyshev, eval_chebyshev_node]
    split_ifs with h
    · rw [pow_one]
      exact dvd_iff_isRoot.mpr hz
    · apply sq_linear_dvd_of_eval_deriv_eq_zero _ _ hz
      simpa [shiftedChebyshev] using deriv_chebyshev_node k i (by omega)

theorem mirrored_product {M : Type*} [CommMonoid M] (k : ℕ) (f : ℕ → M)
    (h : ∀ j ≤ k, f (2*k-j) = f j) :
    (∏ j ∈ range (2*k+1), f j) =
      ∏ j ∈ range (k+1), (f j) ^ (if j = k then 1 else 2 : ℕ) := by
  have ht : (∏ i ∈ range k, f (k+1+i)) = ∏ i ∈ range k, f i := by
    rw [← prod_range_reflect (fun i => f (k+1+i)) k]
    apply prod_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [show k + 1 + (k - 1 - i) = 2 * k - i by omega]
    exact h i (by omega)
  have hh : (∏ i ∈ range k, (f i) ^ (if i = k then 1 else 2 : ℕ)) =
      (∏ i ∈ range k, f i) ^ 2 := by
    rw [← Finset.prod_pow]
    apply prod_congr rfl
    intro i hi
    simp [ne_of_lt (mem_range.mp hi)]
  calc
    _ = ((∏ i ∈ range k, f i) * f k) * ∏ i ∈ range k, f i := by
      rw [show 2*k+1 = (k+1)+k by omega, prod_range_add, ht, prod_range_succ]
    _ = _ := by rw [prod_range_succ, hh]; simp [pow_two, mul_comm, mul_left_comm, mul_assoc]

noncomputable def nodeProduct (k : ℕ) : Polynomial ℝ :=
  ∏ j ∈ range (2*k+1), (X - C (node k j))

theorem nodeProduct_dvd (k : ℕ) : nodeProduct k ∣ shiftedChebyshev k := by
  unfold nodeProduct
  rw [mirrored_product k _ (fun i hi => by rw [node_mirror k i hi])]
  exact characteristic_factors_dvd k

theorem nodeProduct_degree (k : ℕ) : (nodeProduct k).natDegree = 2*k+1 := by
  unfold nodeProduct
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (node k i))]
  simp

theorem nodeProduct_eval_zero_ne (k : ℕ) : (nodeProduct k).eval 0 ≠ 0 := by
  unfold nodeProduct
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro i hi
  simpa using node_ne_zero k i (mem_range.mp hi)

theorem shiftedChebyshev_degree_le (k : ℕ) :
    (shiftedChebyshev k).natDegree ≤ 2*k+1 := by
  unfold shiftedChebyshev
  rw [show 2 * (k : ℤ) + 1 = ((2*k+1 : ℕ) : ℤ) by push_cast <;> ring]
  exact (natDegree_sub_le _ _).trans (by simp)

theorem shiftedChebyshev_is_scalar_mul (k : ℕ) :
    ∃ c : ℝ, shiftedChebyshev k = nodeProduct k * C c := by
  obtain ⟨Q, h⟩ := nodeProduct_dvd k
  by_cases hQ : Q = 0
  · exact ⟨0, by simp [h, hQ]⟩
  have hn : nodeProduct k ≠ 0 := by
    intro h0
    apply nodeProduct_eval_zero_ne k
    simp [h0]
  have hdeg := shiftedChebyshev_degree_le k
  rw [h, natDegree_mul hn hQ, nodeProduct_degree] at hdeg
  exact ⟨Q.coeff 0, by rw [← eq_C_of_natDegree_eq_zero (by omega : Q.natDegree = 0)]; exact h⟩

noncomputable def denominator (k : ℕ) : Polynomial ℝ :=
  ∏ j ∈ range (2*k+1), (1 - C ((node k j)⁻¹) * X)

theorem nodeProduct_normalized (k : ℕ) :
    nodeProduct k = C ((nodeProduct k).eval 0) * denominator k := by
  have hzero : (nodeProduct k).eval 0 = ∏ j ∈ range (2*k+1), -node k j := by
    simp [nodeProduct, eval_prod]
  rw [hzero, map_prod, denominator, ← prod_mul_distrib]
  unfold nodeProduct
  apply prod_congr rfl
  intro j hj
  have h := node_ne_zero k j (mem_range.mp hj)
  have hC : C (node k j) * C ((node k j)⁻¹) = (1 : Polynomial ℝ) := by
    rw [← map_mul]; simp [h]
  rw [map_neg]
  linear_combination -X * hC

theorem denominator_eq_chebyshev (k : ℕ) :
    denominator k = 1 - C ((-1 : ℝ)^k) * Chebyshev.T ℝ (2 * (k : ℤ) + 1) := by
  let s : ℝ := (-1 : ℝ)^k
  have hs : s * s = 1 := by
    unfold s
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hsC : (C s : Polynomial ℝ) * C s = 1 := by rw [← map_mul, hs, map_one]
  have hv : (shiftedChebyshev k).eval 0 = -s := by
    have ho : Odd (2 * (k : ℤ) + 1) := ⟨k, rfl⟩
    simp [shiftedChebyshev, Chebyshev.T_eval_zero_of_odd ℝ ho, s]
  obtain ⟨c, hc⟩ := shiftedChebyshev_is_scalar_mul k
  have hval : (nodeProduct k).eval 0 * c = -s := by
    simpa [hc] using hv
  have hP : shiftedChebyshev k = C (-s) * denominator k := by
    calc
      _ = (C ((nodeProduct k).eval 0) * denominator k) * C c := by
        rw [hc, ← nodeProduct_normalized]
      _ = C ((nodeProduct k).eval 0 * c) * denominator k := by rw [map_mul]; ring
      _ = _ := by rw [hval]
  change denominator k = 1 - C s * Chebyshev.T ℝ (2 * (k : ℤ) + 1)
  change Chebyshev.T ℝ (2 * (k : ℤ) + 1) - C s = C (-s) * denominator k at hP
  rw [map_neg] at hP
  linear_combination (C s) * hP + (1 - denominator k) * hsC

end VerlindeNodes


namespace VerlindeChebyshev

open Polynomial Polynomial.Chebyshev

/-- When `d` is odd, the derivatives of `T_d` at zero, after division by its
first derivative there, are obtained by evaluating these polynomials at `d`. -/
noncomputable def jet : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => 1
  | m + 2 => (C ((m : ℝ) ^ 2) - X ^ 2) * jet m

theorem derivative_eval_zero_of_odd (d : ℤ) (hd : Odd d) (m : ℕ) :
    (Polynomial.derivative^[m] (T ℝ d)).eval 0 =
      (Polynomial.derivative (T ℝ d)).eval 0 * (jet m).eval (d : ℝ) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [jet, T_eval_zero_of_odd ℝ hd]
  | one => simp [jet]
  | more m ih _ =>
    rw [iterate_derivative_T_eval_zero_recurrence, ih]
    simp only [jet, eval_mul, eval_sub, eval_C, eval_pow, eval_X]
    ring

theorem jet_degree (m : ℕ) : (jet (m + 1)).natDegree ≤ m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [jet]
  | one => simp [jet]
  | more m ih _ =>
    change ((C (((m + 1 : ℕ) : ℝ) ^ 2) - X ^ 2) * jet (m + 1)).natDegree ≤ m + 2
    have h : (C (((m + 1 : ℕ) : ℝ) ^ 2) - (X : Polynomial ℝ) ^ 2).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (by simp)
    exact natDegree_mul_le.trans (by omega)

theorem jet_reflect (m : ℕ) (D : ℝ) :
    (jet (m + 1)).eval (-D) = (-1 : ℝ) ^ m * (jet (m + 1)).eval D := by
  induction m using Nat.twoStepInduction with
  | zero => simp [jet]
  | one => simp [jet]
  | more m ih _ =>
    change ((C (((m + 1 : ℕ) : ℝ) ^ 2) - X ^ 2) * jet (m + 1)).eval (-D) =
      (-1 : ℝ) ^ (m + 2) * ((C (((m + 1 : ℕ) : ℝ) ^ 2) - X ^ 2) * jet (m + 1)).eval D
    simp only [eval_mul, eval_sub, eval_C, eval_pow, eval_X]
    rw [ih, pow_add]
    ring

/-- Coefficient of degree `m + 1` in the normalized signed Chebyshev polynomial. -/
noncomputable def scaledJet (m : ℕ) : Polynomial ℝ :=
  C (((m + 1).factorial : ℝ)⁻¹) * jet (m + 1)

theorem scaledJet_degree (m : ℕ) : (scaledJet m).natDegree ≤ m := by
  unfold scaledJet
  exact natDegree_mul_le.trans (by simpa using jet_degree m)

theorem scaledJet_reflect (m : ℕ) (D : ℝ) :
    (scaledJet m).eval (-D) = (-1 : ℝ) ^ m * (scaledJet m).eval D := by
  simp only [scaledJet, eval_mul, eval_C, jet_reflect]
  ring

/-- The coefficients of the logarithmic derivative follow by Cauchy multiplication:
if `G(t) = ∑ scaledJet i · t^(i+1)`, these are the coefficients of `G'/(1-XG)`. -/
noncomputable def momentPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | m + 1 => C ((m : ℝ) + 2) * scaledJet (m + 1) +
      X * ∑ i ∈ Finset.range (m + 1), scaledJet i * momentPolynomial (m - i)
termination_by n => n
decreasing_by omega

theorem momentPolynomial_degree (n : ℕ) : (momentPolynomial n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentPolynomial]
    | succ m =>
      rw [momentPolynomial]
      apply natDegree_add_le_of_degree_le
      · exact natDegree_mul_le.trans (by simpa using scaledJet_degree (m + 1))
      · have hs : (∑ i ∈ Finset.range (m + 1), scaledJet i * momentPolynomial (m - i)).natDegree ≤ m := by
          apply natDegree_sum_le_of_forall_le
          intro i hi
          have hi' : i ≤ m := by simpa using Finset.mem_range.mp hi
          have hd := scaledJet_degree i
          have hm := ih (m - i) (by omega)
          exact natDegree_mul_le.trans (by omega)
        exact natDegree_mul_le.trans (by simp only [natDegree_X]; omega)

theorem momentPolynomial_reflect (n : ℕ) (D : ℝ) :
    (momentPolynomial n).eval (-D) = (-1 : ℝ) ^ n * (momentPolynomial n).eval D := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [momentPolynomial]
    | succ m =>
      rw [momentPolynomial]
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_finsetSum]
      rw [scaledJet_reflect]
      have hs : (∑ i ∈ Finset.range (m + 1),
            (scaledJet i).eval (-D) * (momentPolynomial (m - i)).eval (-D)) =
          (-1 : ℝ) ^ m * ∑ i ∈ Finset.range (m + 1),
            (scaledJet i).eval D * (momentPolynomial (m - i)).eval D := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ m := by simpa using Finset.mem_range.mp hi
        rw [scaledJet_reflect, ih (m - i) (by omega)]
        have hpow : (-1 : ℝ) ^ i * (-1 : ℝ) ^ (m - i) = (-1 : ℝ) ^ m := by
          rw [← pow_add, Nat.add_sub_of_le hi']
        linear_combination ((scaledJet i).eval D * (momentPolynomial (m - i)).eval D) * hpow
      rw [hs, pow_succ]
      ring

/-- Reindexing the odd parameter `D = 2x+1` converts ordinary parity in `D` into
the involution `x ↦ -1-x` on the row parameter. -/
noncomputable def interpolatingPolynomial (n : ℕ) : Polynomial ℝ :=
  (momentPolynomial n).comp (C 2 * X + 1)

theorem interpolatingPolynomial_eval (n : ℕ) (x : ℝ) :
    (interpolatingPolynomial n).eval x = (momentPolynomial n).eval (2 * x + 1) := by
  simp [interpolatingPolynomial, eval_comp]

theorem interpolatingPolynomial_degree (n : ℕ) : (interpolatingPolynomial n).natDegree ≤ n := by
  have ha : ((C 2 : Polynomial ℝ) * X + 1).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (natDegree_mul_le.trans (by simp)) (by simp)
  unfold interpolatingPolynomial
  rw [natDegree_comp]
  exact (Nat.mul_le_mul (momentPolynomial_degree n) ha).trans (by simp)

theorem interpolatingPolynomial_reflect (n : ℕ) (x : ℝ) :
    (interpolatingPolynomial n).eval (-1-x) = (-1 : ℝ)^n * (interpolatingPolynomial n).eval x := by
  rw [interpolatingPolynomial_eval, interpolatingPolynomial_eval,
    show 2 * (-1 - x) + 1 = -(2 * x + 1) by ring, momentPolynomial_reflect]

end VerlindeChebyshev


namespace VerlindeMoments

open Finset

noncomputable def geom (w : ℝ) : PowerSeries ℝ := PowerSeries.mk fun n => w ^ n

noncomputable def factor (w : ℝ) : PowerSeries ℝ := 1 - PowerSeries.C w * PowerSeries.X

theorem factor_geom (w : ℝ) : factor w * geom w = 1 := by
  ext n
  rw [factor, sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [geom]
  | succ n =>
    simp [geom, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, pow_succ, mul_comm]

theorem derivative_factor (w : ℝ) :
    (PowerSeries.derivative ℝ) (factor w) = -PowerSeries.C w := by
  simp [factor, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_one]

noncomputable def denominator {ι : Type*} (s : Finset ι) (w : ι → ℝ) : PowerSeries ℝ :=
  ∏ i ∈ s, factor (w i)

noncomputable def moments {ι : Type*} (s : Finset ι) (w : ι → ℝ) : PowerSeries ℝ :=
  ∑ i ∈ s, PowerSeries.C (w i) * geom (w i)

theorem moments_coeff {ι : Type*} (s : Finset ι) (w : ι → ℝ) (n : ℕ) :
    PowerSeries.coeff n (moments s w) = ∑ i ∈ s, w i ^ (n + 1) := by
  simp [moments, geom, PowerSeries.coeff_C_mul, map_sum, pow_succ, mul_comm]

theorem log_derivative {ι : Type*} (s : Finset ι) (w : ι → ℝ) :
    denominator s w * moments s w = -(PowerSeries.derivative ℝ) (denominator s w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [denominator, moments, PowerSeries.derivative_one]
  | insert i s hi ih =>
    have hD : denominator (insert i s) w = factor (w i) * denominator s w := by
      simp [denominator, hi]
    have hM : moments (insert i s) w = PowerSeries.C (w i) * geom (w i) + moments s w := by
      simp [moments, hi]
    rw [hD, hM, Derivation.leibniz, derivative_factor]
    simp only [smul_eq_mul]
    linear_combination (factor (w i)) * ih +
      (denominator s w * PowerSeries.C (w i)) * factor_geom (w i)

/-- A formal logarithmic derivative determines its coefficients recursively. -/
theorem coefficient_recurrence (F M : PowerSeries ℝ) (d : ℝ) (e : ℕ → ℝ)
    (h0 : PowerSeries.coeff 0 F = 1) (he : ∀ i, PowerSeries.coeff (i+1) F = -d * e i)
    (hFM : F * M = -(PowerSeries.derivative ℝ) F) (n : ℕ) :
    PowerSeries.coeff n M =
      d * ((n + 1) * e n + ∑ i ∈ range n, e i * PowerSeries.coeff (n - 1 - i) M) := by
  have hr := congrArg (PowerSeries.coeff n) hFM
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ,
    sum_range_succ', map_neg, PowerSeries.coeff_derivative] at hr
  simp only [h0, Nat.sub_zero, one_mul, he] at hr
  have ht : (∑ i ∈ range n, -d * e i * PowerSeries.coeff (n - (i+1)) M) =
      -d * ∑ i ∈ range n, e i * PowerSeries.coeff (n - 1 - i) M := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [show n - (i+1) = n - 1 - i by omega]
    ring
  rw [ht] at hr
  linarith only [hr]

end VerlindeMoments

namespace VerlindeAssembly

open Polynomial OMA.S_oeis_a398690

theorem signed_slope (k : ℕ) :
    (derivative (Chebyshev.T ℝ (2 * (k : ℤ) + 1))).eval 0 =
      (2 * (k : ℝ) + 1) * (-1 : ℝ)^k := by
  rw [Chebyshev.T_derivative_eq_U, eval_mul,
    show (2 * (k : ℤ) + 1) - 1 = 2 * (k : ℤ) by ring, Chebyshev.U_eval_two_mul_zero]
  simp [Int.cast_negOnePow_natCast]

theorem signed_chebyshev_coeff (k i : ℕ) :
    (VerlindeNodes.denominator k).coeff (i+1) =
      -(2 * (k : ℝ) + 1) * (VerlindeChebyshev.scaledJet i).eval (2*(k : ℝ)+1) := by
  let d : ℤ := 2 * (k : ℤ) + 1
  have ho : Odd d := ⟨k, rfl⟩
  have hj := VerlindeChebyshev.derivative_eval_zero_of_odd d ho (i+1)
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative] at hj
  simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul] at hj
  dsimp [d] at hj
  rw [signed_slope] at hj
  push_cast at hj
  have hs : (-1 : ℝ)^k * (-1 : ℝ)^k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [VerlindeNodes.denominator_eq_chebyshev, coeff_sub, coeff_C_mul,
    VerlindeChebyshev.scaledJet, eval_mul, eval_C]
  simp only [coeff_one, Nat.succ_ne_zero, if_false, zero_sub]
  field_simp [show ((i+1).factorial : ℝ) ≠ 0 by positivity]
  linear_combination -((-1 : ℝ)^k) * hj -
    ((2*(k:ℝ)+1) * (VerlindeChebyshev.jet (i+1)).eval (2*(k:ℝ)+1)) * hs

theorem denominator_series (k : ℕ) :
    VerlindeMoments.denominator (Finset.range (2*k+1)) (fun j => (VerlindeNodes.node k j)⁻¹) =
      ((VerlindeNodes.denominator k : Polynomial ℝ) : PowerSeries ℝ) := by
  unfold VerlindeMoments.denominator VerlindeNodes.denominator
  change _ = Polynomial.coeToPowerSeries.ringHom _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp [Polynomial.coeToPowerSeries.ringHom_apply, VerlindeMoments.factor]

theorem original_moments (k n : ℕ) :
    PowerSeries.coeff n (VerlindeMoments.moments (Finset.range (2*k+1))
      (fun j => (VerlindeNodes.node k j)⁻¹)) = (2*(k : ℝ)+1) * rowValue n k := by
  rw [VerlindeMoments.moments_coeff, VerlindeNodes.rowValue_eq_moments]
  field_simp [show 2 * (k : ℝ) + 1 ≠ 0 by positivity]

theorem interpolation_identity (k n : ℕ) :
    rowValue n k = (VerlindeChebyshev.momentPolynomial n).eval (2*(k : ℝ)+1) := by
  let d : ℝ := 2*(k : ℝ)+1
  let s := Finset.range (2*k+1)
  let w := fun j => (VerlindeNodes.node k j)⁻¹
  let F := VerlindeMoments.denominator s w
  let M := VerlindeMoments.moments s w
  let e := fun i => (VerlindeChebyshev.scaledJet i).eval d
  have hf : F = ((VerlindeNodes.denominator k : Polynomial ℝ) : PowerSeries ℝ) :=
    denominator_series k
  have h0 : PowerSeries.coeff 0 F = 1 := by
    rw [hf, Polynomial.coeff_coe, coeff_zero_eq_eval_zero]
    simp [VerlindeNodes.denominator, eval_prod]
  have he (i : ℕ) : PowerSeries.coeff (i+1) F = -d * e i := by
    rw [hf, Polynomial.coeff_coe]
    exact signed_chebyshev_coeff k i
  have hM (m : ℕ) : PowerSeries.coeff m M = d * rowValue m k := original_moments k m
  have hrec := VerlindeMoments.coefficient_recurrence F M d e h0 he (VerlindeMoments.log_derivative s w)
  have hd : d ≠ 0 := by dsimp [d]; positivity
  change rowValue n k = (VerlindeChebyshev.momentPolynomial n).eval d
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := hrec n
    rw [hM] at h
    have ht := (mul_left_cancel₀ hd h)
    cases n with
    | zero => simpa [e, VerlindeChebyshev.momentPolynomial, VerlindeChebyshev.scaledJet,
        VerlindeChebyshev.jet] using ht
    | succ m =>
      have hs : (∑ i ∈ Finset.range (m+1), e i * PowerSeries.coeff (m+1-1-i) M) =
          d * ∑ i ∈ Finset.range (m+1),
            e i * (VerlindeChebyshev.momentPolynomial (m-i)).eval d := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.add_sub_cancel, hM]
        rw [ih (m-i) (by omega)]
        ring
      rw [hs] at ht
      rw [VerlindeChebyshev.momentPolynomial]
      simpa [e, eval_finsetSum, Nat.cast_add, add_assoc] using ht

end VerlindeAssembly

theorem OMA.solution : type_of% @OMA.S_oeis_a398690.main := by
  apply VerlindeReflection.main_of_reflected_rows
  intro n
  refine ⟨VerlindeChebyshev.interpolatingPolynomial n, VerlindeChebyshev.interpolatingPolynomial_degree n, ?_,
    VerlindeChebyshev.interpolatingPolynomial_reflect n⟩
  intro k
  rw [VerlindeChebyshev.interpolatingPolynomial_eval]
  exact VerlindeAssembly.interpolation_identity k n

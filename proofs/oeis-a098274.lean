import OMAStatements.S_oeis_a098274
import Mathlib

/-!
# The two congruences for OEIS A098274

Credit: @dwilfand-sys (formalization by Codex). Peter Bala proposed the two
congruences for this sequence. @sntntHb formalized the target in PR #8455.
Zudilin's signed-binomial identity relates this sequence to the family in
Coster's 1989 Theorem 4. The mathematical result already follows from that
work. We give a direct proof using the positive sum defining the sequence.

The binomial ratio lemmas are from @TheWaler's PR #5983. The unit reciprocal
blocks and summation by parts adapt the argument developed for A181069,
following Jacobsthal and the binomial congruence methods of Osburn, Sahu
and Straub. Half-block reflection handles the extra factor at 2j+1.
Source: https://oeis.org/A098274
-/

/-!
# Robert–Zuber's binomial ratio with exact prime-power precision

The following valuation library and ratio proof were formalized by @TheWaler
for A208425 in upstream PR #5983. The source credits Hao Pan and Zhi-Wei Sun,
Frontiers in Combinatorics and Number Theory 2 (2026), 55–62, Section 3.
This excerpt contains the dependencies of the ratio and integer divisibility
lemmas used in A181069. The namespace is local to this proof. The source is
pinned at https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/5f89a85efbb27661dada0165b238cd5b0a647ec7/proofs/OeisA208425.conjecture_1.lean .
-/

namespace A181069.RobertZuber

open Finset BigOperators

def ValPGe (p m : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ q = (p : ℚ) ^ m * (a : ℚ) / (b : ℚ)

lemma valPGe_zero (p : ℕ) (hp : p.Prime) (m : ℕ) : ValPGe p m 0 :=
  ⟨0, 1, fun h => hp.not_dvd_one h, by simp⟩

lemma valPGe_mono {p m₁ m₂ : ℕ} {q : ℚ} (h : m₁ ≤ m₂) (hq : ValPGe p m₂ q) : ValPGe p m₁ q := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨(p : ℤ) ^ (m₂ - m₁) * a, b, hb, ?_⟩
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le h]

lemma valPGe_neg {p m : ℕ} {q : ℚ} (hq : ValPGe p m q) : ValPGe p m (-q) := by
  rcases hq with ⟨a, b, hb, rfl⟩
  refine ⟨-a, b, hb, ?_⟩
  push_cast; ring

lemma valPGe_add {p : ℕ} (hp : p.Prime) {m : ℕ} {q₁ q₂ : ℚ}
    (h₁ : ValPGe p m q₁) (h₂ : ValPGe p m q₂) : ValPGe p m (q₁ + q₂) := by
  rcases h₁ with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hb₁ (h0 ▸ dvd_zero p)
  have hb₂0 : (b₂ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hb₂ (h0 ▸ dvd_zero p)
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, fun h => (hp.dvd_mul.1 h).elim hb₁ hb₂, ?_⟩
  push_cast
  field_simp [hb₁0, hb₂0]

lemma valPGe_sub {p : ℕ} (hp : p.Prime) {m : ℕ} {q₁ q₂ : ℚ}
    (h₁ : ValPGe p m q₁) (h₂ : ValPGe p m q₂) : ValPGe p m (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact valPGe_add hp h₁ (valPGe_neg h₂)

lemma valPGe_mul {p : ℕ} (hp : p.Prime) {m₁ m₂ : ℕ} {q₁ q₂ : ℚ}
    (h₁ : ValPGe p m₁ q₁) (h₂ : ValPGe p m₂ q₂) : ValPGe p (m₁ + m₂) (q₁ * q₂) := by
  rcases h₁ with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, fun h => (hp.dvd_mul.1 h).elim hb₁ hb₂, ?_⟩
  push_cast; rw [pow_add]; ring

lemma valPGe_pow {p : ℕ} (hp : p.Prime) {m : ℕ} {q : ℚ} (hq : ValPGe p m q) :
    ∀ k : ℕ, ValPGe p (k * m) (q ^ k)
  | 0 => ⟨1, 1, fun h => hp.not_dvd_one h, by simp⟩
  | k + 1 => by
    rw [pow_succ, show (k + 1) * m = k * m + m by ring]
    exact valPGe_mul hp (valPGe_pow hp hq k) hq

lemma valPGe_sum {ι : Type*} {p : ℕ} (hp : p.Prime) (S : Finset ι) (m : ℕ) (f : ι → ℚ)
    (hf : ∀ i ∈ S, ValPGe p m (f i)) : ValPGe p m (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using valPGe_zero p hp m
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact valPGe_add hp (hf a (Finset.mem_insert_self a S))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma valPGe_intCast_zero (p : ℕ) (hp : p.Prime) (z : ℤ) : ValPGe p 0 (z : ℚ) :=
  ⟨z, 1, fun h => hp.not_dvd_one h, by simp⟩

lemma valPGe_natCast_padicValNat {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ValPGe p (padicValNat p n) (n : ℚ) := by
  set v := padicValNat p n
  have hdvd : p ^ v ∣ n := pow_padicValNat_dvd
  rcases hdvd with ⟨q, hq⟩
  refine ⟨(q : ℤ), 1, fun h => hp.not_dvd_one h, ?_⟩
  conv_lhs => rw [hq]
  push_cast; ring

lemma valPGe_div_nat_of_not_dvd {p m b : ℕ} (hp : p.Prime) (hb : ¬ p ∣ b) {q : ℚ}
    (hq : ValPGe p m q) : ValPGe p m (q / (b : ℚ)) := by
  rcases hq with ⟨a, b₁, hb₁, rfl⟩
  refine ⟨a, b₁ * b, fun h => (hp.dvd_mul.1 h).elim hb₁ hb, ?_⟩
  push_cast; ring

lemma valPGe_div_one_add {p m : ℕ} (hp : p.Prime) {u q : ℚ}
    (hu : ValPGe p 1 u) (hq : ValPGe p m q) : ValPGe p m (q / (1 + u)) := by
  rcases hu with ⟨a₁, b₁, hb₁, rfl⟩
  rcases hq with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hb₁ (h0 ▸ dvd_zero p)
  set num : ℤ := (b₁ : ℤ) + (p : ℤ) * a₁
  have hnot_num : ¬ (p : ℤ) ∣ num := by
    intro h
    have h1 : (p : ℤ) ∣ (b₁ : ℤ) := by
      have hsub : (p : ℤ) ∣ num - (p : ℤ) * a₁ := dvd_sub h (dvd_mul_right _ _)
      simpa [num] using hsub
    exact hb₁ (Int.natCast_dvd_natCast.1 h1)
  have hnot_abs : ¬ p ∣ num.natAbs := fun h => hnot_num (Int.natCast_dvd.2 h)
  have h1u : 1 + (p : ℚ) ^ 1 * (a₁ : ℚ) / (b₁ : ℚ) = (num : ℚ) / (b₁ : ℚ) := by
    simp only [num, pow_one]; push_cast; field_simp [hb₁0]
  have habs0 : (num.natAbs : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hnot_abs (h0 ▸ dvd_zero p)
  rcases Int.natAbs_eq num with hpos | hneg
  · have hnumQ : (num : ℚ) = (num.natAbs : ℚ) := by simpa using congrArg ((↑) : ℤ → ℚ) hpos
    refine ⟨a₂ * (b₁ : ℤ), b₂ * num.natAbs, fun h => (hp.dvd_mul.1 h).elim hb₂ hnot_abs, ?_⟩
    rw [h1u, hnumQ]; push_cast
    field_simp [hb₁0, habs0]
  · have hnumQ : (num : ℚ) = -(num.natAbs : ℚ) := by simpa using congrArg ((↑) : ℤ → ℚ) hneg
    refine ⟨-(a₂ * (b₁ : ℤ)), b₂ * num.natAbs, fun h => (hp.dvd_mul.1 h).elim hb₂ hnot_abs, ?_⟩
    rw [h1u, hnumQ]; push_cast
    field_simp [hb₁0, habs0]

lemma valPGe_pow_div_nat {p m j : ℕ} (hp : p.Prime) (hj : j ≠ 0) (hle : padicValNat p j ≤ m) :
    ValPGe p (m - padicValNat p j) ((p : ℚ) ^ m / (j : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p j
  rcases (pow_padicValNat_dvd : p ^ v ∣ j) with ⟨u, hu⟩
  have hu' : j = p ^ v * u := hu
  have hnotu : ¬ p ∣ u := by
    intro hpu
    rcases hpu with ⟨r, rfl⟩
    have hd : p ^ (v + 1) ∣ j := ⟨r, by rw [hu', pow_succ]; ring⟩
    have := (padicValNat_dvd_iff_le hj).1 hd
    omega
  have hpv0 : (p : ℚ) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨1, u, hnotu, ?_⟩
  rw [hu']; push_cast
  have hexp : (p : ℚ) ^ m = (p : ℚ) ^ (m - v) * (p : ℚ) ^ v := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hexp]
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hnotu (h0 ▸ dvd_zero p)
  field_simp [hpv0, hu0]

lemma valPGe_div_nat_general {p m j : ℕ} (hp : p.Prime) (hj : j ≠ 0)
    (hle : padicValNat p j ≤ m) {q : ℚ} (hq : ValPGe p m q) :
    ValPGe p (m - padicValNat p j) (q / (j : ℚ)) := by
  rcases hq with ⟨a, b, hb, rfl⟩
  have hdiv := valPGe_pow_div_nat hp hj hle
  have h1 := valPGe_mul hp hdiv (valPGe_div_nat_of_not_dvd hp hb (valPGe_intCast_zero p hp a))
  rw [add_zero] at h1
  convert h1 using 1
  ring

lemma dvd_of_valPGe_int {p m : ℕ} (hp : p.Prime) {z : ℤ} (h : ValPGe p m (z : ℚ)) :
    ((p ^ m : ℕ) : ℤ) ∣ z := by
  rcases h with ⟨a, b, hb, hq⟩
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hb (h0 ▸ dvd_zero p)
  have heqQ : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ m * (a : ℚ) := by
    rw [hq]; field_simp [hb0]
  have heqZ : z * (b : ℤ) = ((p ^ m : ℕ) : ℤ) * a := by exact_mod_cast heqQ
  have hcop : IsCoprime ((p ^ m : ℕ) : ℤ) (b : ℤ) := by
    have hnat : Nat.Coprime (p ^ m) b := (hp.coprime_iff_not_dvd.2 hb).pow_left m
    exact Nat.isCoprime_iff_coprime.2 hnat
  exact hcop.dvd_of_dvd_mul_right ⟨a, heqZ⟩

lemma padicValNat_lt_self {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) : padicValNat p j < j := by
  have : Fact p.Prime := ⟨hp⟩
  have hpv : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
  have hle : p ^ padicValNat p j ≤ j := Nat.le_of_dvd (by omega) hpv
  have h2 : padicValNat p j < 2 ^ padicValNat p j := Nat.lt_two_pow_self
  have hp2 : 2 ^ padicValNat p j ≤ p ^ padicValNat p j := Nat.pow_le_pow_left hp.two_le _
  omega

lemma four_mul_le_five_pow_sub_one (v : ℕ) (hv : 1 ≤ v) : 4 * v ≤ 5 ^ v - 1 := by
  induction v with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => norm_num
    | succ m =>
      have h1 := ih (by omega)
      have hpos : 1 ≤ 5 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      have h5 : 5 ^ (m + 2) = 5 * 5 ^ (m + 1) := by ring
      omega

lemma four_mul_padicValNat_le {p m : ℕ} (hp : p.Prime) (hpgt3 : 3 < p) (hm : 1 ≤ m) :
    4 * padicValNat p m ≤ m - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hv : padicValNat p m = 0
  · rw [hv]; omega
  · have hv1 : 1 ≤ padicValNat p m := by omega
    have hp5 : 5 ≤ p := by
      rcases hp.eq_two_or_odd with rfl | hodd <;> omega
    have hpow : 5 ^ padicValNat p m ≤ m :=
      (Nat.pow_le_pow_left hp5 _).trans (Nat.le_of_dvd (by omega) pow_padicValNat_dvd)
    have h4 := four_mul_le_five_pow_sub_one (padicValNat p m) hv1
    omega

/- ### Part 3: Truncated Logarithm Additivity and Injectivity -/

def truncLog (E : ℕ) (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * x ^ j

lemma valPGe_of_truncLog_valPGe {p E : ℕ} (hp : p.Prime) {u : ℚ}
    (hu2 : ValPGe p 2 u) (hlog : ValPGe p E (truncLog E u)) : ValPGe p E u := by
  have hstep : ∀ k : ℕ, k ≤ E → ValPGe p k u := by
    intro k
    induction k with
    | zero => intro _; exact valPGe_mono (by omega) hu2
    | succ k ih =>
      intro hkE
      by_cases hk2 : k + 1 ≤ 2
      · exact valPGe_mono hk2 hu2
      · have hk_ge2 : 2 ≤ k := by omega
        have huk : ValPGe p k u := ih (by omega)
        have hE1 : 1 ≤ E := by omega
        have hsplit : truncLog E u = u +
            ∑ j ∈ Finset.Icc 2 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * u ^ j := by
          unfold truncLog
          have hIcc : Finset.Icc 1 E = insert 1 (Finset.Icc 2 E) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp)]
          simp
        have hu_eq : u = truncLog E u -
            ∑ j ∈ Finset.Icc 2 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * u ^ j := by linarith
        rw [hu_eq]
        refine valPGe_sub hp (valPGe_mono hkE hlog) (valPGe_sum hp _ _ _ fun j hj => ?_)
        have hj2 : 2 ≤ j := (Finset.mem_Icc.1 hj).1
        have hvalj : padicValNat p j < j := padicValNat_lt_self hp (by omega)
        have hjk : k + 1 ≤ j * k - padicValNat p j := by
          have hmul : j + k ≤ j * k := by nlinarith
          omega
        have huj : ValPGe p (j * k) (u ^ j) := valPGe_pow hp huk j
        have hterm : ValPGe p (j * k - padicValNat p j) (u ^ j / (j : ℚ)) :=
          valPGe_div_nat_general hp (by omega) (by omega) huj
        have hsign : ValPGe p 0 ((-1 : ℚ) ^ (j - 1)) := by
          have : (-1 : ℚ) ^ (j - 1) = (((-1 : ℤ) ^ (j - 1) : ℤ) : ℚ) := by push_cast; rfl
          rw [this]; exact valPGe_intCast_zero p hp _
        have hmul_val := valPGe_mul hp hsign hterm
        rw [zero_add] at hmul_val
        have hrew : ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * u ^ j =
            (-1 : ℚ) ^ (j - 1) * (u ^ j / (j : ℚ)) := by ring
        rw [hrew]
        exact valPGe_mono hjk hmul_val
  exact hstep E le_rfl

lemma poly_valPGe_coeff_mul {p : ℕ} (hp : p.Prime) {f g : Polynomial ℚ}
    (hf : ∀ k, ValPGe p 0 (f.coeff k)) (hg : ∀ k, ValPGe p 0 (g.coeff k)) (k : ℕ) :
    ValPGe p 0 ((f * g).coeff k) := by
  rw [Polynomial.coeff_mul]
  refine valPGe_sum hp _ 0 _ fun x _ => ?_
  simpa using valPGe_mul hp (hf x.1) (hg x.2)

lemma poly_valPGe_coeff_pow {p : ℕ} (hp : p.Prime) {f : Polynomial ℚ}
    (hf : ∀ k, ValPGe p 0 (f.coeff k)) : ∀ j k, ValPGe p 0 ((f ^ j).coeff k)
  | 0, k => by
    rw [pow_zero, Polynomial.coeff_one]
    split_ifs
    · exact valPGe_intCast_zero p hp 1
    · exact valPGe_zero p hp 0
  | j + 1, k => by
    rw [pow_succ]
    exact poly_valPGe_coeff_mul hp (poly_valPGe_coeff_pow hp hf j) hf k

lemma truncLogPoly_deriv_mul (E : ℕ) (u : Polynomial ℚ) :
    (1 + u) * Polynomial.derivative
      (∑ j ∈ Finset.Icc 1 E, Polynomial.C ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * u ^ j) =
      (1 - (-u) ^ E) * Polynomial.derivative u := by
  rw [map_sum]
  have hderiv : ∑ j ∈ Finset.Icc 1 E,
      Polynomial.derivative (Polynomial.C ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * u ^ j) =
      (∑ r ∈ Finset.range E, (-u) ^ r) * Polynomial.derivative u := by
    rw [Finset.sum_mul]
    refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj; exact Finset.mem_range.2 (by omega)
    · intro j₁ hj₁ j₂ hj₂ hEq
      simp only [Finset.mem_Icc] at hj₁ hj₂; omega
    · intro r hr
      simp only [Finset.mem_range] at hr
      exact ⟨r + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow]
      have hC : Polynomial.C ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * Polynomial.C (j : ℚ) * u ^ (j - 1) =
          (-u) ^ (j - 1) := by
        rw [← Polynomial.C_mul, div_mul_cancel₀ _ hj0, neg_eq_neg_one_mul u, mul_pow]
        simp
      rw [← mul_assoc, ← mul_assoc, hC]
  rw [hderiv, ← mul_assoc]
  congr 1
  have hgeom := geom_sum_mul (-u) E
  have hsub : (1 : Polynomial ℚ) + u = -((-u) - 1) := by ring
  have hgoal : (1 + u) * ∑ r ∈ Finset.range E, (-u) ^ r = 1 - (-u) ^ E := by
    calc (1 + u) * ∑ r ∈ Finset.range E, (-u) ^ r
        = -((∑ r ∈ Finset.range E, (-u) ^ r) * ((-u) - 1)) := by ring
      _ = -((-u) ^ E - 1) := by rw [hgeom]
      _ = 1 - (-u) ^ E := by ring
  exact hgoal

lemma coeff_eq_zero_of_mul_unit_dvd_X_pow {E : ℕ} {h f : Polynomial ℚ}
    (hh0 : h.coeff 0 = 1) (hdvd : Polynomial.X ^ E ∣ h * f) :
    ∀ k < E, f.coeff k = 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkE
    have hcoeff0 : (h * f).coeff k = 0 := by
      rcases hdvd with ⟨q, hq⟩
      rw [hq, Polynomial.coeff_X_pow_mul']
      rw [if_neg (by omega)]
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => h.coeff i * f.coeff j)] at hcoeff0
    rw [Finset.sum_range_succ'] at hcoeff0
    have hrest : ∑ i ∈ Finset.range k, h.coeff (i + 1) * f.coeff (k - (i + 1)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hik : i < k := Finset.mem_range.1 hi
      rw [ih (k - (i + 1)) (by omega) (by omega), mul_zero]
    rw [hrest, zero_add, Nat.sub_zero, hh0, one_mul] at hcoeff0
    exact hcoeff0

lemma valPGe_truncLog_mul {p E : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : ValPGe p 2 x) (hy : ValPGe p 2 y) :
    ValPGe p E (truncLog E (x + y + x * y) - (truncLog E x + truncLog E y)) := by
  by_cases hE0 : E = 0
  · subst hE0; simp [truncLog]; exact valPGe_zero p hp 0
  rcases hx with ⟨ax, bx, hbx, hx_eq⟩
  rcases hy with ⟨ay, by_, hby, hy_eq⟩
  set a : ℚ := (ax : ℚ) / (bx : ℚ)
  set b : ℚ := (ay : ℚ) / (by_ : ℚ)
  have ha0 : ValPGe p 0 a := ⟨ax, bx, hbx, by simp [a]⟩
  have hb0 : ValPGe p 0 b := ⟨ay, by_, hby, by simp [b]⟩
  have hx' : x = (p : ℚ) ^ 2 * a := by rw [hx_eq]; simp [a]; ring
  have hy' : y = (p : ℚ) ^ 2 * b := by rw [hy_eq]; simp [b]; ring
  let u₁ : Polynomial ℚ := Polynomial.C a * Polynomial.X
  let u₂ : Polynomial ℚ := Polynomial.C b * Polynomial.X
  let u₃ : Polynomial ℚ := u₁ + u₂ + u₁ * u₂
  let L : Polynomial ℚ → Polynomial ℚ := fun u =>
    ∑ j ∈ Finset.Icc 1 E, Polynomial.C ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * u ^ j
  let g : Polynomial ℚ := L u₃ - (L u₁ + L u₂)
  have heval : g.eval ((p : ℚ) ^ 2) =
      truncLog E (x + y + x * y) - (truncLog E x + truncLog E y) := by
    have hLeval : ∀ u : Polynomial ℚ, (L u).eval ((p : ℚ) ^ 2) = truncLog E (u.eval ((p : ℚ) ^ 2)) := by
      intro u
      simp only [L, truncLog, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow]
    have hu1e : u₁.eval ((p : ℚ) ^ 2) = x := by
      simp only [u₁, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [hx', mul_comm]
    have hu2e : u₂.eval ((p : ℚ) ^ 2) = y := by
      simp only [u₂, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [hy', mul_comm]
    have hu3e : u₃.eval ((p : ℚ) ^ 2) = x + y + x * y := by
      simp only [u₃, Polynomial.eval_add, Polynomial.eval_mul, hu1e, hu2e]
    simp only [g, Polynomial.eval_sub, Polynomial.eval_add, hLeval, hu1e, hu2e, hu3e]
  -- Show `g.coeff k = 0` for all `k ≤ E`
  have hg_zero : ∀ k ≤ E, g.coeff k = 0 := by
    have hdvd_deriv : Polynomial.X ^ E ∣ ((1 + u₁) * (1 + u₂)) * Polynomial.derivative g := by
      have h1 : (1 + u₁) * Polynomial.derivative (L u₁) = (1 - (-u₁) ^ E) * Polynomial.derivative u₁ :=
        truncLogPoly_deriv_mul E u₁
      have h2 : (1 + u₂) * Polynomial.derivative (L u₂) = (1 - (-u₂) ^ E) * Polynomial.derivative u₂ :=
        truncLogPoly_deriv_mul E u₂
      have h3 : (1 + u₃) * Polynomial.derivative (L u₃) = (1 - (-u₃) ^ E) * Polynomial.derivative u₃ :=
        truncLogPoly_deriv_mul E u₃
      have h13 : 1 + u₃ = (1 + u₁) * (1 + u₂) := by dsimp [u₃]; ring
      have hdu3 : Polynomial.derivative u₃ =
          (1 + u₂) * Polynomial.derivative u₁ + (1 + u₁) * Polynomial.derivative u₂ := by
        have hdm : Polynomial.derivative (u₁ * u₂) =
            Polynomial.derivative u₁ * u₂ + u₁ * Polynomial.derivative u₂ :=
          Polynomial.derivative_mul
        have hstep : Polynomial.derivative (u₁ + u₂ + u₁ * u₂) =
            Polynomial.derivative u₁ + Polynomial.derivative u₂ + Polynomial.derivative (u₁ * u₂) := by
          rw [map_add, map_add]
        change Polynomial.derivative (u₁ + u₂ + u₁ * u₂) = _
        rw [hstep, hdm]; ring
      have hid : ((1 + u₁) * (1 + u₂)) * Polynomial.derivative g =
          -((-u₃) ^ E * Polynomial.derivative u₃) +
          (1 + u₂) * ((-u₁) ^ E * Polynomial.derivative u₁) +
          (1 + u₁) * ((-u₂) ^ E * Polynomial.derivative u₂) := by
        have hg_d : Polynomial.derivative g =
            Polynomial.derivative (L u₃) - (Polynomial.derivative (L u₁) + Polynomial.derivative (L u₂)) := by
          dsimp [g]; rw [map_sub, map_add]
        rw [hg_d]
        have hstep1 : ((1 + u₁) * (1 + u₂)) * Polynomial.derivative (L u₃) =
            (1 - (-u₃) ^ E) * Polynomial.derivative u₃ := by rw [← h13, h3]
        have hstep2 : ((1 + u₁) * (1 + u₂)) * Polynomial.derivative (L u₁) =
            (1 + u₂) * ((1 - (-u₁) ^ E) * Polynomial.derivative u₁) := by
          rw [← h1]; ring
        have hstep3 : ((1 + u₁) * (1 + u₂)) * Polynomial.derivative (L u₂) =
            (1 + u₁) * ((1 - (-u₂) ^ E) * Polynomial.derivative u₂) := by
          rw [← h2]; ring
        calc ((1 + u₁) * (1 + u₂)) *
              (Polynomial.derivative (L u₃) - (Polynomial.derivative (L u₁) + Polynomial.derivative (L u₂)))
            = ((1 + u₁) * (1 + u₂)) * Polynomial.derivative (L u₃) -
              ((1 + u₁) * (1 + u₂)) * Polynomial.derivative (L u₁) -
              ((1 + u₁) * (1 + u₂)) * Polynomial.derivative (L u₂) := by ring
          _ = (1 - (-u₃) ^ E) * Polynomial.derivative u₃ -
              (1 + u₂) * ((1 - (-u₁) ^ E) * Polynomial.derivative u₁) -
              (1 + u₁) * ((1 - (-u₂) ^ E) * Polynomial.derivative u₂) := by
                rw [hstep1, hstep2, hstep3]
          _ = _ := by rw [hdu3]; ring
      rw [hid]
      have hXu1 : Polynomial.X ∣ -u₁ := ⟨-Polynomial.C a, by dsimp [u₁]; ring⟩
      have hXu2 : Polynomial.X ∣ -u₂ := ⟨-Polynomial.C b, by dsimp [u₂]; ring⟩
      have hXu3 : Polynomial.X ∣ -u₃ :=
        ⟨-(Polynomial.C a + Polynomial.C b + Polynomial.C a * Polynomial.C b * Polynomial.X), by
          dsimp [u₃, u₁, u₂]; ring⟩
      refine dvd_add (dvd_add ?_ ?_) ?_
      · exact (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu3 E) _).neg_right
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu1 E) _) _
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu2 E) _) _
    have hconst : ((1 + u₁) * (1 + u₂)).coeff 0 = 1 := by
      simp [u₁, u₂, Polynomial.coeff_mul]
    have hderiv0 := coeff_eq_zero_of_mul_unit_dvd_X_pow hconst hdvd_deriv
    intro k hkE
    cases k with
    | zero =>
      have : g.eval 0 = 0 := by
        have hL0 : ∀ u : Polynomial ℚ, u.eval 0 = 0 → (L u).eval 0 = 0 := by
          intro u hu0
          simp only [L, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, hu0]
          refine Finset.sum_eq_zero fun j hj => ?_
          have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
          rw [zero_pow (by omega), mul_zero]
        have hu10 : u₁.eval 0 = 0 := by simp [u₁]
        have hu20 : u₂.eval 0 = 0 := by simp [u₂]
        have hu30 : u₃.eval 0 = 0 := by simp [u₃, hu10, hu20]
        simp [g, hL0 _ hu10, hL0 _ hu20, hL0 _ hu30]
      rw [Polynomial.coeff_zero_eq_eval_zero]; exact this
    | succ m =>
      have hd := hderiv0 m (by omega)
      rw [Polynomial.coeff_derivative] at hd
      have hm0 : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.1 hd).resolve_right hm0
  -- Show `ValPGe p 0 ((p : ℚ)^E * g.coeff k)` for every `k`
  have hu1_val : ∀ k, ValPGe p 0 (u₁.coeff k) := by
    intro k
    simp only [u₁, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    split_ifs
    · simpa using ha0
    · simpa using valPGe_zero p hp 0
  have hu2_val : ∀ k, ValPGe p 0 (u₂.coeff k) := by
    intro k
    simp only [u₂, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    split_ifs
    · simpa using hb0
    · simpa using valPGe_zero p hp 0
  have hu3_val : ∀ k, ValPGe p 0 (u₃.coeff k) := by
    intro k
    simp only [u₃, Polynomial.coeff_add]
    exact valPGe_add hp (valPGe_add hp (hu1_val k) (hu2_val k))
      (poly_valPGe_coeff_mul hp hu1_val hu2_val k)
  have hg_val : ∀ k, ValPGe p 0 ((p : ℚ) ^ E * g.coeff k) := by
    have hL_val : ∀ u : Polynomial ℚ, (∀ k, ValPGe p 0 (u.coeff k)) →
        ∀ k, ValPGe p 0 ((p : ℚ) ^ E * (L u).coeff k) := by
      intro u hu k
      simp only [L, Polynomial.finsetSum_coeff, Finset.mul_sum, Polynomial.coeff_C_mul]
      refine valPGe_sum hp _ 0 _ fun j hj => ?_
      have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
      have hjE : j ≤ E := (Finset.mem_Icc.1 hj).2
      have hvpj : padicValNat p j ≤ E := (padicValNat_lt_self hp hj1).le.trans hjE
      have hdiv := valPGe_mono (Nat.zero_le _) (valPGe_pow_div_nat hp (by omega : j ≠ 0) hvpj)
      have hsign : ValPGe p 0 ((-1 : ℚ) ^ (j - 1)) := by
        have : (-1 : ℚ) ^ (j - 1) = (((-1 : ℤ) ^ (j - 1) : ℤ) : ℚ) := by push_cast; rfl
        rw [this]; exact valPGe_intCast_zero p hp _
      have h1 := valPGe_mul hp (valPGe_mul hp hsign hdiv) (poly_valPGe_coeff_pow hp hu j k)
      rw [zero_add, zero_add] at h1
      convert h1 using 1
      ring
    intro k
    simp only [g, Polynomial.coeff_sub, Polynomial.coeff_add, mul_sub, mul_add]
    exact valPGe_sub hp (hL_val u₃ hu3_val k) (valPGe_add hp (hL_val u₁ hu1_val k) (hL_val u₂ hu2_val k))
  rw [← heval, Polynomial.eval_eq_sum_range]
  refine valPGe_sum hp _ E _ fun k _ => ?_
  by_cases hk : k ≤ E
  · rw [hg_zero k hk, zero_mul]; exact valPGe_zero p hp E
  · have hge : E ≤ 2 * k - E := by omega
    have hpow : ((p : ℚ) ^ 2) ^ k = (p : ℚ) ^ (2 * k - E) * (p : ℚ) ^ E := by
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    have hrew : g.coeff k * ((p : ℚ) ^ (2 * k - E) * (p : ℚ) ^ E) =
        (p : ℚ) ^ (2 * k - E) * ((p : ℚ) ^ E * g.coeff k) := by ring
    rw [hrew]
    have hp_term : ValPGe p (2 * k - E) ((p : ℚ) ^ (2 * k - E)) :=
      ⟨1, 1, fun h => hp.not_dvd_one h, by simp⟩
    have hprod := valPGe_mul hp hp_term (hg_val k)
    rw [add_zero] at hprod
    exact valPGe_mono hge hprod

lemma valPGe_truncLog_prod {ι : Type*} {p E : ℕ} (hp : p.Prime)
    (S : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ S, ValPGe p 2 (x i)) :
    ValPGe p 2 ((∏ i ∈ S, (1 + x i)) - 1) ∧
    ValPGe p E (truncLog E ((∏ i ∈ S, (1 + x i)) - 1) - ∑ i ∈ S, truncLog E (x i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using valPGe_zero p hp 2, ?_⟩
    have h0 : truncLog E 0 = 0 := by
      unfold truncLog
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [zero_pow (by have := (Finset.mem_Icc.1 hj).1; omega), mul_zero]
    simp [h0, valPGe_zero p hp E]
  | insert a S ha ih =>
    have hxa : ValPGe p 2 (x a) := hx a (Finset.mem_insert_self a S)
    obtain ⟨hS2, hSlog⟩ := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    set y : ℚ := (∏ i ∈ S, (1 + x i)) - 1
    have hprod_eq : (∏ i ∈ insert a S, (1 + x i)) - 1 = x a + y + x a * y := by
      rw [Finset.prod_insert ha]
      simp only [y]; ring
    rw [hprod_eq, Finset.sum_insert ha]
    refine ⟨?_, ?_⟩
    · exact valPGe_add hp (valPGe_add hp hxa hS2) (valPGe_mono (by omega) (valPGe_mul hp hxa hS2))
    · have hmul := valPGe_truncLog_mul (E := E) hp hxa hS2
      have hcomb := valPGe_add hp hmul hSlog
      convert hcomb using 1
      ring

lemma valPGe_truncLog_div {p E : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : ValPGe p 2 x) (hy : ValPGe p 2 y) :
    ValPGe p 2 ((1 + x) / (1 + y) - 1) ∧
    ValPGe p E (truncLog E ((1 + x) / (1 + y) - 1) - (truncLog E x - truncLog E y)) := by
  have hy1 : ValPGe p 1 y := valPGe_mono (by omega) hy
  have hy_ne : 1 + y ≠ 0 := by
    rcases hy1 with ⟨a, b, hb, rfl⟩
    intro h0
    have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
    have hnum : (b : ℤ) + (p : ℤ) * a = 0 := by
      have : ((b : ℚ) + (p : ℚ) * (a : ℚ)) / (b : ℚ) = 0 := by
        rw [← h0]; simp only [pow_one]; field_simp [hb0]
      have := (div_eq_zero_iff.1 this).resolve_right hb0
      exact_mod_cast this
    have hdvd : (p : ℤ) ∣ (b : ℤ) := ⟨-a, by linarith⟩
    exact hb (Int.natCast_dvd_natCast.1 hdvd)
  set z : ℚ := (x - y) / (1 + y)
  have hz_eq : (1 + x) / (1 + y) - 1 = z := by
    simp only [z]; field_simp [hy_ne]; ring
  have hz2 : ValPGe p 2 z := valPGe_div_one_add hp hy1 (valPGe_sub hp hx hy)
  have hxy : y + z + y * z = x := by
    simp only [z]; field_simp [hy_ne]; ring
  rw [hz_eq]
  refine ⟨hz2, ?_⟩
  have hmul := valPGe_truncLog_mul (E := E) hp hy hz2
  rw [hxy] at hmul
  have hneg := valPGe_neg hmul
  convert hneg using 1
  ring

/- ### Part 4: Wolstenholme's `S_2 ≡ 0 (mod p)` and Odd Polynomials `Q_j(N)` -/

lemma wolstenholme_T1 {p : ℕ} (hp : p.Prime) (hpgt3 : 3 < p) :
    ValPGe p 1 (∑ r ∈ Finset.Icc 1 (p - 1), (((r * (p - r) : ℕ) : ℚ)⁻¹)) := by
  have : Fact p.Prime := ⟨hp⟩
  -- In `ZMod p`, `∑_{r=1}^{p-1} (r * (p - r))⁻¹ = - ∑_{r=1}^{p-1} r⁻¹ ^ 2 = 0`
  have hsum_zmod : (∑ x : ZMod p, (x⁻¹) ^ 2) = 0 := by
    let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) (by
      intro h2
      have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by simpa using h2)
      have := Nat.le_of_dvd (by norm_num) hd; omega)
    have hshift : (∑ x : ZMod p, (x⁻¹) ^ 2) = ∑ x : ZMod p, ((e x)⁻¹) ^ 2 :=
      (Equiv.sum_comp e (fun x => (x⁻¹) ^ 2)).symm
    have h4 : (∑ x : ZMod p, ((e x)⁻¹) ^ 2) = (4 : ZMod p)⁻¹ * (∑ x : ZMod p, (x⁻¹) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      change ((2 * x)⁻¹) ^ 2 = (4 : ZMod p)⁻¹ * (x⁻¹) ^ 2
      rw [mul_inv, mul_pow, show ((2 : ZMod p)⁻¹) ^ 2 = (4 : ZMod p)⁻¹ by
        rw [inv_pow]; congr 1; norm_num]
    have hmul4 : (4 : ZMod p) * (∑ x : ZMod p, (x⁻¹) ^ 2) = (∑ x : ZMod p, (x⁻¹) ^ 2) := by
      have h4ne : (4 : ZMod p) ≠ 0 := by
        intro h40
        have hd : p ∣ 2 * 2 := (ZMod.natCast_eq_zero_iff 4 p).1 (by simpa using h40)
        rcases hp.dvd_mul.1 hd with h2 | h2 <;>
          (have := Nat.le_of_dvd (by norm_num) h2; omega)
      calc (4 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2
          = (4 : ZMod p) * ((4 : ZMod p)⁻¹ * ∑ x : ZMod p, (x⁻¹) ^ 2) := by rw [← h4, ← hshift]
        _ = ∑ x : ZMod p, (x⁻¹) ^ 2 := by rw [← mul_assoc, mul_inv_cancel₀ h4ne, one_mul]
    have h3 : (3 : ZMod p) * (∑ x : ZMod p, (x⁻¹) ^ 2) = 0 := by
      calc (3 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2
          = (4 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 2 - ∑ x : ZMod p, (x⁻¹) ^ 2 := by ring
        _ = 0 := sub_eq_zero.2 hmul4
    have h3ne : (3 : ZMod p) ≠ 0 := by
      intro h30
      have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by simpa using h30)
      have := Nat.le_of_dvd (by norm_num) hd; omega
    exact (mul_eq_zero.1 h3).resolve_left h3ne
  -- Common denominator `D = ∏_{r=1}^{p-1} (r * (p - r))`, coprime to `p`
  let D : ℕ := ∏ r ∈ Finset.Icc 1 (p - 1), (r * (p - r))
  have hnotD : ¬ p ∣ D := by
    intro hd
    rw [Prime.dvd_finsetProd_iff hp.prime] at hd
    obtain ⟨r, hr, hpr⟩ := hd
    simp only [Finset.mem_Icc] at hr
    rcases hp.dvd_mul.1 hpr with h1 | h2
    · have := Nat.le_of_dvd (by omega) h1; omega
    · have := Nat.le_of_dvd (by omega) h2; omega
  let N : ℕ := ∑ r ∈ Finset.Icc 1 (p - 1), (D / (r * (p - r)))
  have hsum_eq : ∑ r ∈ Finset.Icc 1 (p - 1), (((r * (p - r) : ℕ) : ℚ)⁻¹) = (N : ℚ) / (D : ℚ) := by
    have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h0 => hnotD (h0 ▸ dvd_zero p)
    rw [eq_div_iff hD0, Finset.sum_mul]
    simp only [N, Nat.cast_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_dvd : r * (p - r) ∣ D := Finset.dvd_prod_of_mem _ hr
    have hr0 : ((r * (p - r) : ℕ) : ℚ) ≠ 0 := by
      simp only [Finset.mem_Icc] at hr
      exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have hmul : ((D / (r * (p - r)) : ℕ) : ℚ) * ((r * (p - r) : ℕ) : ℚ) = (D : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hr_dvd
    field_simp [hr0]
    linarith
  have hp_dvd_N : p ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hDne : (D : ZMod p) ≠ 0 := fun h => hnotD ((ZMod.natCast_eq_zero_iff D p).1 h)
    have hterm : ∀ r ∈ Finset.Icc 1 (p - 1),
        ((D / (r * (p - r)) : ℕ) : ZMod p) = -(D : ZMod p) * ((r : ZMod p)⁻¹) ^ 2 := by
      intro r hr
      have hr_dvd : r * (p - r) ∣ D := Finset.dvd_prod_of_mem _ hr
      have hr_le : r ≤ p := by simp only [Finset.mem_Icc] at hr; omega
      have hrne : (r : ZMod p) ≠ 0 := by
        intro h0
        have hd := (ZMod.natCast_eq_zero_iff r p).1 h0
        simp only [Finset.mem_Icc] at hr
        have := Nat.le_of_dvd (by omega) hd; omega
      have hprod_z : ((r * (p - r) : ℕ) : ZMod p) = -((r : ZMod p) ^ 2) := by
        rw [Nat.cast_mul, Nat.cast_sub hr_le, ZMod.natCast_self, zero_sub]; ring
      have hmul_z : ((D / (r * (p - r)) : ℕ) : ZMod p) * ((r * (p - r) : ℕ) : ZMod p) = (D : ZMod p) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hr_dvd]
      rw [hprod_z] at hmul_z
      have hinv : ((r : ZMod p) ^ 2) * ((r : ZMod p)⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hrne, one_pow]
      calc ((D / (r * (p - r)) : ℕ) : ZMod p)
          = ((D / (r * (p - r)) : ℕ) : ZMod p) * (((r : ZMod p) ^ 2) * ((r : ZMod p)⁻¹) ^ 2) := by
              rw [hinv, mul_one]
        _ = -(((D / (r * (p - r)) : ℕ) : ZMod p) * -((r : ZMod p) ^ 2)) * ((r : ZMod p)⁻¹) ^ 2 := by ring
        _ = -(D : ZMod p) * ((r : ZMod p)⁻¹) ^ 2 := by rw [hmul_z]
    simp only [N, Nat.cast_sum]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hbij : ∑ r ∈ Finset.Icc 1 (p - 1), ((r : ZMod p)⁻¹) ^ 2 = ∑ x : ZMod p, (x⁻¹) ^ 2 := by
      have hp1 : 0 < p := hp.pos
      have h0 : ((0 : ZMod p)⁻¹) ^ 2 = 0 := by simp
      have huniv : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ k ∈ Finset.range p, (((k : ZMod p)⁻¹) ^ 2) := by
        refine (Finset.sum_bij (fun (k : ℕ) _ => (k : ZMod p)) ?_ ?_ ?_ (fun _ _ => rfl)).symm
        · intro _ _; exact Finset.mem_univ _
        · intro k₁ hk₁ k₂ hk₂ hEq
          simp only [Finset.mem_range] at hk₁ hk₂
          have h1 := congrArg ZMod.val hEq
          rwa [ZMod.val_natCast_of_lt hk₁, ZMod.val_natCast_of_lt hk₂] at h1
        · intro x _
          exact ⟨x.val, Finset.mem_range.2 (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
      rw [huniv]
      have hrange : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
        ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_add]
    rw [hbij, hsum_zmod, mul_zero]
  rcases hp_dvd_N with ⟨q, hq⟩
  refine ⟨(q : ℤ), D, hnotD, ?_⟩
  rw [hsum_eq, hq]; push_cast; ring

lemma odd_pow_sub_dvd (a b : ℤ) :
    ∀ r : ℕ, 1 ≤ r → a * b * (a + b) ∣ ((a + b) ^ (2 * r + 1) - a ^ (2 * r + 1) - b ^ (2 * r + 1))
  | 0, hr => by omega
  | 1, _ => ⟨3, by ring⟩
  | r + 2, _ => by
    obtain ⟨q, hq⟩ := odd_pow_sub_dvd a b (r + 1) (by omega)
    let S : ℤ := ∑ i ∈ Finset.range (2 * (r + 1) + 1), (-1 : ℤ) ^ i * a ^ i * b ^ (2 * (r + 1) - i)
    have hS : (a + b) * S = a ^ (2 * (r + 1) + 1) + b ^ (2 * (r + 1) + 1) := by
      have hsum : (a + b) * S =
          (∑ i ∈ Finset.range (2 * (r + 1) + 1), (-1 : ℤ) ^ i * a ^ (i + 1) * b ^ (2 * (r + 1) - i)) +
          (∑ i ∈ Finset.range (2 * (r + 1) + 1), (-1 : ℤ) ^ i * a ^ i * b ^ (2 * (r + 1) + 1 - i)) := by
        rw [add_mul, Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_
        · ring
        · have hi' : i ≤ 2 * (r + 1) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [show 2 * (r + 1) + 1 - i = (2 * (r + 1) - i) + 1 by omega, pow_succ]; ring
      rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ']
      have hcancel : (∑ i ∈ Finset.range (2 * (r + 1)),
            (-1 : ℤ) ^ i * a ^ (i + 1) * b ^ (2 * (r + 1) - i)) +
          (∑ i ∈ Finset.range (2 * (r + 1)),
            (-1 : ℤ) ^ (i + 1) * a ^ (i + 1) * b ^ (2 * (r + 1) + 1 - (i + 1))) = 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [show 2 * (r + 1) + 1 - (i + 1) = 2 * (r + 1) - i by omega, pow_succ]; ring
      have heven : (-1 : ℤ) ^ (2 * (r + 1)) = 1 := by
        rw [pow_mul]; norm_num
      have hlast : (-1 : ℤ) ^ (2 * (r + 1)) * a ^ (2 * (r + 1) + 1) * b ^ (2 * (r + 1) - 2 * (r + 1)) =
          a ^ (2 * (r + 1) + 1) := by rw [heven, Nat.sub_self]; ring
      have hfirst : (-1 : ℤ) ^ 0 * a ^ 0 * b ^ (2 * (r + 1) + 1 - 0) = b ^ (2 * (r + 1) + 1) := by
        simp
      rw [hlast, hfirst]
      linarith
    refine ⟨(a + b) ^ 2 * q + (a ^ (2 * (r + 1)) + b ^ (2 * (r + 1)) + S), ?_⟩
    have hrec : (a + b) ^ (2 * (r + 2) + 1) - a ^ (2 * (r + 2) + 1) - b ^ (2 * (r + 2) + 1) =
        (a + b) ^ 2 * ((a + b) ^ (2 * (r + 1) + 1) - a ^ (2 * (r + 1) + 1) - b ^ (2 * (r + 1) + 1)) +
        a * b * ((a + b) * (a ^ (2 * (r + 1)) + b ^ (2 * (r + 1))) + (a ^ (2 * (r + 1) + 1) + b ^ (2 * (r + 1) + 1))) := by
      have e1 : 2 * (r + 2) + 1 = (2 * (r + 1) + 1) + 2 := by omega
      have e2 : 2 * (r + 1) + 1 = 2 * (r + 1) + 1 := rfl
      rw [e1, pow_add, pow_add, pow_add, pow_succ a (2 * (r + 1)), pow_succ b (2 * (r + 1))]
      ring
    rw [hrec, hq, ← hS]; ring

noncomputable def fallPoly : ℕ → Polynomial ℤ
  | 0 => 1
  | r + 1 => fallPoly r * (Polynomial.X - Polynomial.C (r : ℤ))

lemma fallPoly_natDegree (r : ℕ) : (fallPoly r).natDegree = r ∧ (fallPoly r).Monic := by
  induction r with
  | zero => exact ⟨by simp [fallPoly], Polynomial.monic_one⟩
  | succ r ih =>
    have hlin : (Polynomial.X - Polynomial.C (r : ℤ)).Monic := Polynomial.monic_X_sub_C _
    have hmul := ih.2.mul hlin
    refine ⟨?_, hmul⟩
    rw [fallPoly, ih.2.natDegree_mul hlin, ih.1, Polynomial.natDegree_X_sub_C]

lemma fallPoly_diff (r : ℕ) :
    (fallPoly (r + 1)).comp (Polynomial.X + 1) - fallPoly (r + 1) =
      Polynomial.C ((r + 1 : ℕ) : ℤ) * fallPoly r := by
  have hprod : ∀ k : ℕ, (fallPoly (k + 1)).comp (Polynomial.X + 1) =
      (Polynomial.X + 1) * fallPoly k := by
    intro k
    induction k with
    | zero => simp [fallPoly]
    | succ k ih =>
      rw [fallPoly, Polynomial.mul_comp, ih, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.C_comp, fallPoly]
      have hsub : (Polynomial.X + 1 : Polynomial ℤ) - Polynomial.C ((k + 1 : ℕ) : ℤ) =
          Polynomial.X - Polynomial.C (k : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
      rw [hsub]; ring
  rw [hprod r, fallPoly]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring

lemma fallPoly_eval_zero (r : ℕ) : (fallPoly (r + 1)).eval 0 = 0 := by
  induction r with
  | zero => simp [fallPoly]
  | succ r ih => rw [fallPoly, Polynomial.eval_mul, ih, zero_mul]

lemma exists_fallPoly_repr : ∀ (d : ℕ) (P : Polynomial ℤ), P.natDegree ≤ d →
    ∃ c : ℕ → ℤ, P = ∑ r ∈ Finset.range (d + 1), Polynomial.C (c r) * fallPoly r
  | 0, P, hP => by
    refine ⟨fun _ => P.coeff 0, ?_⟩
    rw [Finset.sum_range_one, fallPoly, mul_one]
    exact Polynomial.eq_C_of_natDegree_le_zero hP
  | d + 1, P, hP => by
    let lead : ℤ := P.coeff (d + 1)
    let Q : Polynomial ℤ := P - Polynomial.C lead * fallPoly (d + 1)
    have hQdeg : Q.natDegree ≤ d := by
      apply Polynomial.natDegree_le_iff_coeff_eq_zero.2
      intro k hk
      simp only [Q, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      by_cases hkeq : k = d + 1
      · subst hkeq
        have hmon := (fallPoly_natDegree (d + 1)).2
        have hdeg := (fallPoly_natDegree (d + 1)).1
        have hc : (fallPoly (d + 1)).coeff (d + 1) = 1 := by
          have hlc := hmon.leadingCoeff
          rwa [Polynomial.leadingCoeff, hdeg] at hlc
        rw [hc, mul_one, sub_self]
      · have hgt : d + 1 < k := by omega
        have hP0 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hF0 : (fallPoly (d + 1)).coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [(fallPoly_natDegree (d + 1)).1]; omega)
        rw [hP0, hF0, mul_zero, sub_zero]
    obtain ⟨c, hc⟩ := exists_fallPoly_repr d Q hQdeg
    refine ⟨fun r => if r = d + 1 then lead else c r, ?_⟩
    rw [Finset.sum_range_succ]
    dsimp only
    rw [if_pos rfl]
    have hrest : ∑ r ∈ Finset.range (d + 1),
        Polynomial.C (if r = d + 1 then lead else c r) * fallPoly r = Q := by
      rw [hc]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne : r ≠ d + 1 := by have := Finset.mem_range.1 hr; omega
      rw [if_neg hne]
    rw [hrest]
    simp only [Q]; ring

lemma coeff_comp_neg_X_aux (Q : Polynomial ℚ) (k : ℕ) :
    (Q.comp (-Polynomial.X)).coeff k = (-1 : ℚ) ^ k * Q.coeff k := by
  induction Q using Polynomial.induction_on' with
  | add f g ihf ihg =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, ihf, ihg]; ring
  | monomial n a =>
    have hnegX : (-Polynomial.X : Polynomial ℚ) ^ n =
        Polynomial.C ((-1 : ℚ) ^ n) * Polynomial.X ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow]; simp
    rw [Polynomial.monomial_comp, hnegX, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
    by_cases h : k = n
    · subst h; simp [mul_comm]
    · have h' : n ≠ k := Ne.symm h; simp [h, h']

lemma sum_range_two_mul_split (f : ℕ → ℚ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k =
      (∑ r ∈ Finset.range m, f (2 * r)) + (∑ r ∈ Finset.range m, f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

def QSum (j N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N, ((m * (m + 1) : ℕ) : ℚ) ^ j

lemma QSum_one (N : ℕ) : QSum 1 N = ((N : ℚ) ^ 3 - (N : ℚ)) / 3 := by
  induction N with
  | zero => simp [QSum]
  | succ N ih =>
    unfold QSum at ih ⊢
    rw [Finset.sum_range_succ, ih]
    push_cast; ring

lemma exists_QSum_poly (j : ℕ) :
    ∃ (c : ℕ → ℚ),
      (∀ r, ∃ f : ℕ → ℤ, c r = ∑ d ∈ Finset.range (2 * j + 1), (f d : ℚ) / ((d + 1 : ℕ) : ℚ)) ∧
      (∀ N : ℕ, QSum j N = ∑ r ∈ Finset.range (j + 1), c r * (N : ℚ) ^ (2 * r + 1)) := by
  let P : Polynomial ℤ := (Polynomial.X * (Polynomial.X + 1)) ^ j
  have hPdeg : P.natDegree ≤ 2 * j := by
    have h1 : (Polynomial.X * (Polynomial.X + 1) : Polynomial ℤ).natDegree ≤ 2 := by
      have hX1 : (Polynomial.X + 1 : Polynomial ℤ).natDegree ≤ 1 := by
        calc (Polynomial.X + 1 : Polynomial ℤ).natDegree
            ≤ max (Polynomial.X : Polynomial ℤ).natDegree (1 : Polynomial ℤ).natDegree :=
              Polynomial.natDegree_add_le _ _
          _ ≤ 1 := by simp
      calc (Polynomial.X * (Polynomial.X + 1) : Polynomial ℤ).natDegree
          ≤ (Polynomial.X : Polynomial ℤ).natDegree + (Polynomial.X + 1 : Polynomial ℤ).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 1 + 1 := by rw [Polynomial.natDegree_X]; omega
        _ = 2 := rfl
    calc P.natDegree ≤ j * (Polynomial.X * (Polynomial.X + 1) : Polynomial ℤ).natDegree :=
          Polynomial.natDegree_pow_le
      _ ≤ j * 2 := Nat.mul_le_mul_left j h1
      _ = 2 * j := by ring
  obtain ⟨α, hα⟩ := exists_fallPoly_repr (2 * j) P hPdeg
  let Q : Polynomial ℚ :=
    ∑ d ∈ Finset.range (2 * j + 1),
      Polynomial.C ((α d : ℚ) / ((d + 1 : ℕ) : ℚ)) * (fallPoly (d + 1)).map (Int.castRingHom ℚ)
  have hQ0 : Q.eval 0 = 0 := by
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    refine Finset.sum_eq_zero fun d _ => ?_
    have h0 : (0 : ℚ) = Int.castRingHom ℚ 0 := by simp
    rw [h0, Polynomial.eval_map_apply, fallPoly_eval_zero]; simp
  have hQdiff : Q.comp (Polynomial.X + 1) - Q = P.map (Int.castRingHom ℚ) := by
    have hcomp_sum : Q.comp (Polynomial.X + 1) =
        ∑ d ∈ Finset.range (2 * j + 1),
          (Polynomial.C ((α d : ℚ) / ((d + 1 : ℕ) : ℚ)) *
            (fallPoly (d + 1)).map (Int.castRingHom ℚ)).comp (Polynomial.X + 1) := by
      dsimp only [Q]
      exact map_sum (Polynomial.compRingHom (Polynomial.X + 1)) _ _
    rw [hcomp_sum]
    dsimp only [Q]
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ d ∈ Finset.range (2 * j + 1),
        (Polynomial.C ((α d : ℚ) / ((d + 1 : ℕ) : ℚ)) *
          (fallPoly (d + 1)).map (Int.castRingHom ℚ)).comp (Polynomial.X + 1) -
        Polynomial.C ((α d : ℚ) / ((d + 1 : ℕ) : ℚ)) *
          (fallPoly (d + 1)).map (Int.castRingHom ℚ) =
        Polynomial.C (α d : ℚ) * (fallPoly d).map (Int.castRingHom ℚ) := by
      intro d _
      rw [Polynomial.mul_comp, Polynomial.C_comp, ← mul_sub]
      have hmap_diff : ((fallPoly (d + 1)).map (Int.castRingHom ℚ)).comp (Polynomial.X + 1) -
          (fallPoly (d + 1)).map (Int.castRingHom ℚ) =
          Polynomial.C ((d + 1 : ℕ) : ℚ) * (fallPoly d).map (Int.castRingHom ℚ) := by
        have hcomp : ((fallPoly (d + 1)).map (Int.castRingHom ℚ)).comp (Polynomial.X + 1) =
            ((fallPoly (d + 1)).comp (Polynomial.X + 1)).map (Int.castRingHom ℚ) := by
          rw [Polynomial.map_comp]; simp
        rw [hcomp, ← Polynomial.map_sub, fallPoly_diff d, Polynomial.map_mul, Polynomial.map_C]
        simp
      rw [hmap_diff, ← mul_assoc, ← Polynomial.C_mul,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (by omega))]
    rw [Finset.sum_congr rfl hterm, hα, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun d _ => by simp
  have hQeval : ∀ N : ℕ, Q.eval (N : ℚ) = QSum j N := by
    intro N
    induction N with
    | zero => simpa [QSum] using hQ0
    | succ N ih =>
      unfold QSum at ih ⊢
      rw [Finset.sum_range_succ, ← ih]
      have hd := congrArg (Polynomial.eval (N : ℚ)) hQdiff
      simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one] at hd
      have hPeval : (P.map (Int.castRingHom ℚ)).eval (N : ℚ) = ((N * (N + 1) : ℕ) : ℚ) ^ j := by
        simp [P]
      rw [hPeval] at hd
      push_cast at hd ⊢; linarith
  -- Prove `Q` is an odd polynomial: `Q(-X) = -Q(X)`
  have hQodd : Q.comp (-Polynomial.X) = -Q := by
    let D : Polynomial ℚ := Q + Q.comp (-Polynomial.X)
    have hDnat : ∀ N : ℕ, D.eval (N : ℚ) = 0 := by
      intro N
      induction N with
      | zero => simp [D, hQ0]
      | succ N ih =>
        have h1 : Q.eval ((N : ℚ) + 1) - Q.eval (N : ℚ) = ((N : ℚ) * ((N : ℚ) + 1)) ^ j := by
          have hd := congrArg (Polynomial.eval (N : ℚ)) hQdiff
          simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
            Polynomial.eval_X, Polynomial.eval_one, P, Polynomial.map_pow, Polynomial.map_mul,
            Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.eval_pow,
            Polynomial.eval_mul] at hd
          exact hd
        have h2 : Q.eval (-(N : ℚ)) - Q.eval (-((N : ℚ) + 1)) = ((N : ℚ) * ((N : ℚ) + 1)) ^ j := by
          have hd := congrArg (Polynomial.eval (-((N : ℚ) + 1))) hQdiff
          simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
            Polynomial.eval_X, Polynomial.eval_one, P, Polynomial.map_pow, Polynomial.map_mul,
            Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, Polynomial.eval_pow,
            Polynomial.eval_mul] at hd
          have heq1 : -((N : ℚ) + 1) + 1 = -(N : ℚ) := by ring
          have heq2 : -((N : ℚ) + 1) * (-(N : ℚ)) = (N : ℚ) * ((N : ℚ) + 1) := by ring
          rw [heq1, heq2] at hd
          exact hd
        have hD0 : Q.eval (N : ℚ) + Q.eval (-(N : ℚ)) = 0 := by
          simpa [D, Polynomial.eval_comp] using ih
        have hgoal : Q.eval ((N : ℚ) + 1) + Q.eval (-((N : ℚ) + 1)) = 0 := by linarith
        simpa [D, Polynomial.eval_comp, Nat.cast_succ] using hgoal
    have hDzero : D = 0 := by
      by_contra hne
      have hfin : (D.roots.toFinset).card < (Finset.range (D.roots.toFinset.card + 1)).card := by
        simp
      have hsub : (Finset.range (D.roots.toFinset.card + 1)).image (fun N : ℕ => (N : ℚ)) ⊆
          D.roots.toFinset := by
        intro x hx
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hx
        exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hne).2 (hDnat N))
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range] at hcard
      omega
    exact eq_neg_of_add_eq_zero_right hDzero
  have hQeven : ∀ r : ℕ, Q.coeff (2 * r) = 0 := by
    intro r
    have h := congrArg (fun f : Polynomial ℚ => f.coeff (2 * r)) hQodd
    rw [coeff_comp_neg_X_aux, Polynomial.coeff_neg] at h
    have hev : (-1 : ℚ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
    rw [hev, one_mul] at h
    linarith
  have hQdeg : Q.natDegree ≤ 2 * j + 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    have hdle : d ≤ 2 * j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hd)
    calc (Polynomial.C ((α d : ℚ) / ((d + 1 : ℕ) : ℚ)) *
            (fallPoly (d + 1)).map (Int.castRingHom ℚ)).natDegree
        ≤ (Polynomial.C ((α d : ℚ) / ((d + 1 : ℕ) : ℚ))).natDegree +
          ((fallPoly (d + 1)).map (Int.castRingHom ℚ)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 0 + (fallPoly (d + 1)).natDegree := by
          rw [Polynomial.natDegree_C]
          exact Nat.add_le_add_left Polynomial.natDegree_map_le 0
      _ = d + 1 := by rw [zero_add, (fallPoly_natDegree (d + 1)).1]
      _ ≤ 2 * j + 1 := by omega
  refine ⟨fun r => Q.coeff (2 * r + 1), ?_, ?_⟩
  · intro r
    refine ⟨fun d => α d * (fallPoly (d + 1)).coeff (2 * r + 1), ?_⟩
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Int.coe_castRingHom]
    refine Finset.sum_congr rfl fun d _ => by push_cast; ring
  · intro N
    rw [← hQeval N, Polynomial.eval_eq_sum_range' (show Q.natDegree < 2 * (j + 1) by omega),
      sum_range_two_mul_split (fun k => Q.coeff k * (N : ℚ) ^ k) (j + 1)]
    have hzero : ∑ r ∈ Finset.range (j + 1), Q.coeff (2 * r) * (N : ℚ) ^ (2 * r) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [hQeven r, zero_mul]
    rw [hzero, zero_add]

/- ### Part 5: Factorial Ratio `G(m)`, `H(N)`, and Robert–Zuber Supercongruence -/

def G (p m : ℕ) : ℚ :=
  ∏ r ∈ Finset.Icc 1 (p - 1), (1 + (p * m : ℚ) / (r : ℚ))

def H (p N : ℕ) : ℚ :=
  ∏ m ∈ Finset.range N, G p m

lemma factorial_mul_eq (p N : ℕ) (hp : 1 ≤ p) :
    ((p * N).factorial : ℚ) =
      (((p - 1).factorial : ℚ) * (p : ℚ)) ^ N * (N.factorial : ℚ) * H p N := by
  induction N with
  | zero => simp [H]
  | succ N ih =>
    have hblock : ((p * (N + 1)).factorial : ℚ) =
        ((p * N).factorial : ℚ) * (∏ r ∈ Finset.Icc 1 (p - 1), ((p * N + r : ℕ) : ℚ)) *
          ((p * (N + 1) : ℕ) : ℚ) := by
      have hstep : ∀ t : ℕ, ((p * N + t).factorial : ℚ) =
          ((p * N).factorial : ℚ) * ∏ r ∈ Finset.Icc 1 t, ((p * N + r : ℕ) : ℚ) := by
        intro t
        induction t with
        | zero => simp
        | succ t iht =>
          have hIcc : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp)]
          calc ((p * N + (t + 1)).factorial : ℚ)
              = (((p * N + t) + 1).factorial : ℚ) := rfl
            _ = ((p * N + (t + 1) : ℕ) : ℚ) * ((p * N + t).factorial : ℚ) := by
                rw [Nat.factorial_succ]; push_cast; ring
            _ = ((p * N + (t + 1) : ℕ) : ℚ) *
                (((p * N).factorial : ℚ) * ∏ r ∈ Finset.Icc 1 t, ((p * N + r : ℕ) : ℚ)) := by
                rw [iht]
            _ = _ := by ring
      have h1 := hstep (p - 1)
      have h2 : p * (N + 1) = (p * N + (p - 1)) + 1 := by rw [mul_add, mul_one]; omega
      calc ((p * (N + 1)).factorial : ℚ)
          = (((p * N + (p - 1)) + 1).factorial : ℚ) := by rw [h2]
        _ = ((p * (N + 1) : ℕ) : ℚ) * ((p * N + (p - 1)).factorial : ℚ) := by
            rw [Nat.factorial_succ, ← h2]; push_cast; rfl
        _ = ((p * (N + 1) : ℕ) : ℚ) *
            (((p * N).factorial : ℚ) * ∏ r ∈ Finset.Icc 1 (p - 1), ((p * N + r : ℕ) : ℚ)) := by
            rw [h1]
        _ = _ := by ring
    have hG : ∏ r ∈ Finset.Icc 1 (p - 1), ((p * N + r : ℕ) : ℚ) =
        ((p - 1).factorial : ℚ) * G p N := by
      have hfac : ((p - 1).factorial : ℚ) = ∏ r ∈ Finset.Icc 1 (p - 1), (r : ℚ) := by
        have h : ∀ t : ℕ, (t.factorial : ℚ) = ∏ r ∈ Finset.Icc 1 t, (r : ℚ) := by
          intro t
          induction t with
          | zero => simp
          | succ t iht =>
            have hIcc : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.prod_insert (by simp), ← iht, Nat.factorial_succ]; push_cast; ring
        exact h (p - 1)
      rw [hfac, G, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r hr => ?_
      have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (Finset.mem_Icc.1 hr).1; omega)
      push_cast; field_simp [hr0]; ring
    rw [hblock, ih, hG]
    unfold H
    rw [Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
    push_cast; ring

lemma choose_pn_pk_eq (p n k : ℕ) (hp : 1 ≤ p) (hk : k ≤ n) :
    ((p * n).choose (p * k) : ℚ) * (H p k * H p (n - k)) =
      (n.choose k : ℚ) * H p n := by
  have h1 : ((p * n).choose (p * k) : ℚ) * ((p * k).factorial : ℚ) * ((p * (n - k)).factorial : ℚ) =
      ((p * n).factorial : ℚ) := by
    have hle : p * k ≤ p * n := Nat.mul_le_mul_left p hk
    have := Nat.choose_mul_factorial_mul_factorial hle
    rw [show p * n - p * k = p * (n - k) by rw [Nat.mul_sub_left_distrib]] at this
    exact_mod_cast this
  have h2 : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  rw [factorial_mul_eq p n hp, factorial_mul_eq p k hp, factorial_mul_eq p (n - k) hp] at h1
  set C : ℚ := ((p - 1).factorial : ℚ) * (p : ℚ)
  have hC0 : C ^ n ≠ 0 := by
    have : C ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.2 (by omega))
    exact pow_ne_zero n this
  have hf0 : (k.factorial : ℚ) * ((n - k).factorial : ℚ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hCn : C ^ k * C ^ (n - k) = C ^ n := by rw [← pow_add, Nat.add_sub_of_le hk]
  have heq : C ^ n * ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) *
      (((p * n).choose (p * k) : ℚ) * (H p k * H p (n - k))) =
      C ^ n * ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) * ((n.choose k : ℚ) * H p n) := by
    calc C ^ n * ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) *
          (((p * n).choose (p * k) : ℚ) * (H p k * H p (n - k)))
        = ((p * n).choose (p * k) : ℚ) * (C ^ k * (k.factorial : ℚ) * H p k) *
          (C ^ (n - k) * ((n - k).factorial : ℚ) * H p (n - k)) := by rw [← hCn]; ring
      _ = C ^ n * (n.factorial : ℚ) * H p n := h1
      _ = C ^ n * ((n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ)) * H p n := by rw [h2]
      _ = _ := by ring
  exact mul_left_cancel₀ (mul_ne_zero hC0 hf0) heq

lemma G_sq_eq (p m : ℕ) (hp : 2 ≤ p) :
    (G p m) ^ 2 =
      ∏ r ∈ Finset.Icc 1 (p - 1),
        (1 + ((p : ℚ) ^ 2 * ((m * (m + 1) : ℕ) : ℚ)) / ((r * (p - r) : ℕ) : ℚ)) := by
  have hrev : G p m = ∏ r ∈ Finset.Icc 1 (p - 1), (1 + (p * m : ℚ) / ((p - r : ℕ) : ℚ)) := by
    unfold G
    refine Finset.prod_bij (fun r _ => p - r) ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    · intro r₁ hr₁ r₂ hr₂ hEq; simp only [Finset.mem_Icc] at hr₁ hr₂; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      exact ⟨p - r, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
    · intro r hr; simp only [Finset.mem_Icc] at hr
      rw [show p - (p - r) = r by omega]
  rw [sq]
  conv_lhs => arg 2; rw [hrev]
  unfold G
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  simp only [Finset.mem_Icc] at hr
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpr0 : ((p - r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsum : (r : ℚ) + ((p - r : ℕ) : ℚ) = (p : ℚ) := by
    exact_mod_cast (show r + (p - r) = p by omega)
  push_cast
  field_simp [hr0, hpr0]
  linear_combination ((p : ℚ) * (m : ℚ)) * hsum

lemma valPGe_G_sub_one {p : ℕ} (hp : p.Prime) (m : ℕ) : ValPGe p 1 (G p m - 1) := by
  have hprod : ∀ S : Finset ℕ, (∀ r ∈ S, ValPGe p 1 ((p * m : ℚ) / (r : ℚ))) →
      ValPGe p 1 ((∏ r ∈ S, (1 + (p * m : ℚ) / (r : ℚ))) - 1) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simpa using valPGe_zero p hp 1
    | insert a S ha ih =>
      intro hS
      have h1 := hS a (Finset.mem_insert_self a S)
      have h2 := ih fun r hr => hS r (Finset.mem_insert_of_mem hr)
      rw [Finset.prod_insert ha]
      have hid : (1 + (p * m : ℚ) / (a : ℚ)) * (∏ r ∈ S, (1 + (p * m : ℚ) / (r : ℚ))) - 1 =
          (p * m : ℚ) / (a : ℚ) + ((∏ r ∈ S, (1 + (p * m : ℚ) / (r : ℚ))) - 1) +
          ((p * m : ℚ) / (a : ℚ)) * ((∏ r ∈ S, (1 + (p * m : ℚ) / (r : ℚ))) - 1) := by ring
      rw [hid]
      exact valPGe_add hp (valPGe_add hp h1 h2) (valPGe_mono (by omega) (valPGe_mul hp h1 h2))
  refine hprod (Finset.Icc 1 (p - 1)) fun r hr => ?_
  simp only [Finset.mem_Icc] at hr
  have hnotr : ¬ p ∣ r := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  exact ⟨(m : ℤ), r, hnotr, by simp [pow_one]⟩

lemma valPGe_H_sub_one {p : ℕ} (hp : p.Prime) (N : ℕ) : ValPGe p 1 (H p N - 1) := by
  induction N with
  | zero => simpa [H] using valPGe_zero p hp 1
  | succ N ih =>
    have hG := valPGe_G_sub_one hp N
    rw [H, Finset.prod_range_succ]
    have hid : H p N * G p N - 1 = (H p N - 1) + (G p N - 1) + (H p N - 1) * (G p N - 1) := by
      ring
    change ValPGe p 1 (H p N * G p N - 1)
    rw [hid]
    exact valPGe_add hp (valPGe_add hp ih hG) (valPGe_mono (by omega) (valPGe_mul hp ih hG))

lemma H_ne_zero {p : ℕ} (hp : p.Prime) (N : ℕ) : H p N ≠ 0 := by
  have h1 := valPGe_H_sub_one hp N
  rcases h1 with ⟨a, b, hb, hq⟩
  intro h0
  rw [h0, zero_sub] at hq
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.2 fun h => hb (h ▸ dvd_zero p)
  have heq : -(b : ℚ) = (p : ℚ) * (a : ℚ) := by
    have := congrArg (fun x : ℚ => x * (b : ℚ)) hq
    simp only [pow_one] at this
    field_simp [hb0] at this
    linarith
  have heqZ : -(b : ℤ) = (p : ℤ) * a := by exact_mod_cast heq
  exact hb (Int.natCast_dvd_natCast.1 ⟨-a, by linarith⟩)

lemma robert_zuber_ratio {p : ℕ} (hp : p.Prime) (hpgt3 : 3 < p) (a b : ℕ)
    (_ha : 1 ≤ a) (_hb : 1 ≤ b) :
    ValPGe p (3 + padicValNat p a + padicValNat p b + padicValNat p (a + b))
      (H p (a + b) / (H p a * H p b) - 1) := by
  set E : ℕ := 3 + padicValNat p a + padicValNat p b + padicValNat p (a + b)
  let T : ℕ → ℚ := fun j => ∑ r ∈ Finset.Icc 1 (p - 1), (((r * (p - r) : ℕ) : ℚ)⁻¹) ^ j
  have hT_val : ∀ j : ℕ, ValPGe p 0 (T j) := fun j =>
    valPGe_sum hp _ 0 _ fun r hr => by
      simp only [Finset.mem_Icc] at hr
      have hnot : ¬ p ∣ (r * (p - r)) := fun hd =>
        (hp.dvd_mul.1 hd).elim
          (fun h1 => by have := Nat.le_of_dvd (by omega) h1; omega)
          (fun h2 => by have := Nat.le_of_dvd (by omega) h2; omega)
      have hinv : ValPGe p 0 (((r * (p - r) : ℕ) : ℚ)⁻¹) :=
        ⟨1, r * (p - r), hnot, by simp⟩
      simpa using valPGe_pow hp hinv j
  -- Compute `truncLog E (H p N ^ 2 - 1)` for any `N`
  have hHsq : ∀ N : ℕ,
      ValPGe p 2 (H p N ^ 2 - 1) ∧
      ValPGe p E (truncLog E (H p N ^ 2 - 1) -
        ∑ j ∈ Finset.Icc 1 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j * QSum j N) := by
    intro N
    have hGsq : ∀ m : ℕ,
        ValPGe p 2 (G p m ^ 2 - 1) ∧
        ValPGe p E (truncLog E (G p m ^ 2 - 1) -
          ∑ j ∈ Finset.Icc 1 E,
            ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j *
              ((m * (m + 1) : ℕ) : ℚ) ^ j) := by
      intro m
      have hx : ∀ r ∈ Finset.Icc 1 (p - 1),
          ValPGe p 2 (((p : ℚ) ^ 2 * ((m * (m + 1) : ℕ) : ℚ)) / ((r * (p - r) : ℕ) : ℚ)) := by
        intro r hr
        simp only [Finset.mem_Icc] at hr
        have hnot : ¬ p ∣ (r * (p - r)) := fun hd =>
          (hp.dvd_mul.1 hd).elim
            (fun h1 => by have := Nat.le_of_dvd (by omega) h1; omega)
            (fun h2 => by have := Nat.le_of_dvd (by omega) h2; omega)
        exact ⟨((m * (m + 1) : ℕ) : ℤ), r * (p - r), hnot, by push_cast; rfl⟩
      have hp_prod := valPGe_truncLog_prod (E := E) hp (Finset.Icc 1 (p - 1)) _ hx
      rw [← G_sq_eq p m hp.two_le] at hp_prod
      refine ⟨hp_prod.1, ?_⟩
      have hswap : ∑ r ∈ Finset.Icc 1 (p - 1),
          truncLog E (((p : ℚ) ^ 2 * ((m * (m + 1) : ℕ) : ℚ)) / ((r * (p - r) : ℕ) : ℚ)) =
          ∑ j ∈ Finset.Icc 1 E,
            ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j *
              ((m * (m + 1) : ℕ) : ℚ) ^ j := by
        unfold truncLog
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [T, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [div_pow, mul_pow, ← pow_mul, div_eq_mul_inv, inv_pow]
        ring
      exact hswap ▸ hp_prod.2
    have hHprod : H p N ^ 2 = ∏ m ∈ Finset.range N, (1 + (G p m ^ 2 - 1)) := by
      rw [H, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun m _ => by ring
    have htr := valPGe_truncLog_prod (E := E) hp (Finset.range N) (fun m => G p m ^ 2 - 1)
      (fun m _ => (hGsq m).1)
    rw [← hHprod] at htr
    refine ⟨htr.1, ?_⟩
    have hsum_diff : ValPGe p E ((∑ m ∈ Finset.range N, truncLog E (G p m ^ 2 - 1)) -
        ∑ j ∈ Finset.Icc 1 E,
          ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j * QSum j N) := by
      have hswap : ∑ j ∈ Finset.Icc 1 E,
          ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j * QSum j N =
          ∑ m ∈ Finset.range N, ∑ j ∈ Finset.Icc 1 E,
            ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j *
              ((m * (m + 1) : ℕ) : ℚ) ^ j := by
        unfold QSum
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      rw [hswap, ← Finset.sum_sub_distrib]
      exact valPGe_sum hp _ E _ fun m _ => (hGsq m).2
    have hcomb := valPGe_add hp htr.2 hsum_diff
    convert hcomb using 1
    ring
  -- Combine `H(a+b)^2 / (H(a)^2 * H(b)^2)`
  obtain ⟨hHab2, hHab_log⟩ := hHsq (a + b)
  obtain ⟨hHa2, hHa_log⟩ := hHsq a
  obtain ⟨hHb2, hHb_log⟩ := hHsq b
  set xab : ℚ := H p (a + b) ^ 2 - 1
  set xa : ℚ := H p a ^ 2 - 1
  set xb : ℚ := H p b ^ 2 - 1
  have hprod_ab : ValPGe p 2 (xa + xb + xa * xb) :=
    valPGe_add hp (valPGe_add hp hHa2 hHb2) (valPGe_mono (by omega) (valPGe_mul hp hHa2 hHb2))
  have hmul_ab := valPGe_truncLog_mul (E := E) hp hHa2 hHb2
  obtain ⟨hU2, hU_log⟩ := valPGe_truncLog_div (E := E) hp hHab2 hprod_ab
  set R : ℚ := H p (a + b) / (H p a * H p b)
  have hU_eq : (1 + xab) / (1 + (xa + xb + xa * xb)) - 1 = R ^ 2 - 1 := by
    simp only [xab, xa, xb, R]
    have h1 : 1 + (H p (a + b) ^ 2 - 1) = H p (a + b) ^ 2 := by ring
    have h2 : 1 + (H p a ^ 2 - 1 + (H p b ^ 2 - 1) + (H p a ^ 2 - 1) * (H p b ^ 2 - 1)) =
        (H p a * H p b) ^ 2 := by ring
    rw [h1, h2, div_pow]
  rw [hU_eq] at hU2 hU_log
  -- Prove `ValPGe p E (truncLog E (R^2 - 1))`
  have hΔ_val : ValPGe p E (∑ j ∈ Finset.Icc 1 E,
      ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j *
        (QSum j (a + b) - QSum j a - QSum j b)) := by
    refine valPGe_sum hp _ E _ fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hprod_val : ValPGe p (padicValNat p a + padicValNat p b + padicValNat p (a + b))
        (((a * b * (a + b) : ℕ) : ℚ)) := by
      have h1 := valPGe_mul hp (valPGe_mul hp (valPGe_natCast_padicValNat hp a)
        (valPGe_natCast_padicValNat hp b)) (valPGe_natCast_padicValNat hp (a + b))
      convert h1 using 1; push_cast; ring
    by_cases hj_one : j = 1
    · subst hj_one
      have hQ1 : QSum 1 (a + b) - QSum 1 a - QSum 1 b = ((a * b * (a + b) : ℕ) : ℚ) := by
        rw [QSum_one, QSum_one, QSum_one]; push_cast; ring
      rw [hQ1]
      have hT1 : ValPGe p 1 (T 1) := by
        simpa [T] using wolstenholme_T1 hp hpgt3
      have hp2 : ValPGe p 2 ((p : ℚ) ^ 2) := ⟨1, 1, fun h => hp.not_dvd_one h, by simp⟩
      have hcomb := valPGe_mul hp (valPGe_mul hp hp2 hT1) hprod_val
      convert hcomb using 1
      · simp only [E]; omega
      · norm_num
    · have hj2 : 2 ≤ j := by omega
      obtain ⟨c, hc_form, hQ_poly⟩ := exists_QSum_poly j
      have hΔ_poly : QSum j (a + b) - QSum j a - QSum j b =
          ∑ r ∈ Finset.Icc 1 j,
            c r * (((a + b : ℤ) ^ (2 * r + 1) - (a : ℤ) ^ (2 * r + 1) - (b : ℤ) ^ (2 * r + 1) : ℤ) : ℚ) := by
        rw [hQ_poly (a + b), hQ_poly a, hQ_poly b, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        have hrange : Finset.range (j + 1) = insert 0 (Finset.Icc 1 j) := by
          ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
        rw [hrange, Finset.sum_insert (by simp)]
        have h0 : c 0 * ((a + b : ℕ) : ℚ) ^ 1 - c 0 * (a : ℚ) ^ 1 - c 0 * (b : ℚ) ^ 1 = 0 := by
          push_cast; ring
        simp only [Nat.mul_zero, zero_add, h0]
        refine Finset.sum_congr rfl fun r _ => ?_
        push_cast; ring
      rw [hΔ_poly, Finset.mul_sum]
      refine valPGe_sum hp _ E _ fun r hr => ?_
      have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
      obtain ⟨q_r, hqr⟩ := odd_pow_sub_dvd (a : ℤ) (b : ℤ) r hr1
      obtain ⟨f_r, hfr⟩ := hc_form r
      rw [hqr, hfr, Finset.sum_mul, Finset.mul_sum]
      refine valPGe_sum hp _ E _ fun d hd => ?_
      have hdle : d ≤ 2 * j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hd)
      have hvj : 4 * padicValNat p j ≤ j - 1 := four_mul_padicValNat_le hp hpgt3 (by omega)
      have hvd : 4 * padicValNat p (d + 1) ≤ 2 * j := by
        have := four_mul_padicValNat_le hp hpgt3 (show 1 ≤ d + 1 by omega)
        omega
      have hexp3 : 3 ≤ 2 * j - padicValNat p j - padicValNat p (d + 1) := by
        by_cases hj2' : j = 2
        · subst hj2'
          have hv2 : padicValNat p 2 = 0 := by
            have : Fact p.Prime := ⟨hp⟩
            exact padicValNat.eq_zero_of_not_dvd fun h => by
              have := Nat.le_of_dvd (by norm_num) h; omega
          omega
        · omega
      have h1 : ValPGe p (2 * j - padicValNat p j) ((p : ℚ) ^ (2 * j) / (j : ℚ)) :=
        valPGe_pow_div_nat hp (by omega) (by omega)
      have h2 : ValPGe p (2 * j - padicValNat p j - padicValNat p (d + 1))
          (((p : ℚ) ^ (2 * j) / (j : ℚ)) / ((d + 1 : ℕ) : ℚ)) :=
        valPGe_div_nat_general hp (by omega) (by omega) h1
      have h2' : ValPGe p 3 (((p : ℚ) ^ (2 * j) / (j : ℚ)) / ((d + 1 : ℕ) : ℚ)) :=
        valPGe_mono hexp3 h2
      have hcoef : ValPGe p 0 (((-1 : ℚ) ^ (j - 1)) * T j * (f_r d : ℚ) * (q_r : ℚ)) := by
        have hsign : ValPGe p 0 ((-1 : ℚ) ^ (j - 1)) := by
          have : (-1 : ℚ) ^ (j - 1) = (((-1 : ℤ) ^ (j - 1) : ℤ) : ℚ) := by push_cast; rfl
          rw [this]; exact valPGe_intCast_zero p hp _
        simpa using valPGe_mul hp (valPGe_mul hp (valPGe_mul hp hsign (hT_val j))
          (valPGe_intCast_zero p hp (f_r d))) (valPGe_intCast_zero p hp q_r)
      have htot := valPGe_mul hp (valPGe_mul hp h2' hprod_val) hcoef
      convert htot using 1
      · simp [E]; omega
      · push_cast; ring
  have hlog_R2 : ValPGe p E (truncLog E (R ^ 2 - 1)) := by
    have hdiff_logs : ValPGe p E ((truncLog E xab - (truncLog E xa + truncLog E xb)) -
        ∑ j ∈ Finset.Icc 1 E,
          ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j *
            (QSum j (a + b) - QSum j a - QSum j b)) := by
      have h1 := valPGe_sub hp (valPGe_sub hp hHab_log hHa_log) hHb_log
      have hlin : ∑ j ∈ Finset.Icc 1 E,
          ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j *
            (QSum j (a + b) - QSum j a - QSum j b) =
          (∑ j ∈ Finset.Icc 1 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j * QSum j (a + b)) -
          (∑ j ∈ Finset.Icc 1 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j * QSum j a) -
          (∑ j ∈ Finset.Icc 1 E, ((-1 : ℚ) ^ (j - 1) / (j : ℚ)) * (p : ℚ) ^ (2 * j) * T j * QSum j b) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      convert h1 using 1
      rw [hlin]; ring
    have hcomb := valPGe_add hp (valPGe_add hp (valPGe_sub hp hU_log hmul_ab) hdiff_logs) hΔ_val
    convert hcomb using 1
    ring
  have hR2_val : ValPGe p E (R ^ 2 - 1) := valPGe_of_truncLog_valPGe hp hU2 hlog_R2
  -- Unsquare: `R - 1 = (R^2 - 1) / (2 * (1 + (R - 1) / 2))`
  have hR1 : ValPGe p 1 (R - 1) := by
    have h1 := valPGe_H_sub_one hp (a + b)
    have h2 := valPGe_H_sub_one hp a
    have h3 := valPGe_H_sub_one hp b
    have hHaHb : ValPGe p 1 (H p a * H p b - 1) := by
      have hid : H p a * H p b - 1 = (H p a - 1) + (H p b - 1) + (H p a - 1) * (H p b - 1) := by ring
      rw [hid]
      exact valPGe_add hp (valPGe_add hp h2 h3) (valPGe_mono (by omega) (valPGe_mul hp h2 h3))
    have hnum : ValPGe p 1 (H p (a + b) - H p a * H p b) := by
      have : H p (a + b) - H p a * H p b = (H p (a + b) - 1) - (H p a * H p b - 1) := by ring
      rw [this]; exact valPGe_sub hp h1 hHaHb
    have hdiv := valPGe_div_one_add hp hHaHb hnum
    have hrew : (H p (a + b) - H p a * H p b) / (1 + (H p a * H p b - 1)) = R - 1 := by
      have hha : H p a ≠ 0 := H_ne_zero hp a
      have hhb : H p b ≠ 0 := H_ne_zero hp b
      simp only [R]; field_simp [hha, hhb]; ring
    rwa [hrew] at hdiv
  have hnot2 : ¬ p ∣ 2 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hhalf : ValPGe p 1 ((R - 1) / (2 : ℕ)) := valPGe_div_nat_of_not_dvd hp hnot2 hR1
  have hstep1 : ValPGe p E ((R ^ 2 - 1) / (2 : ℕ)) := valPGe_div_nat_of_not_dvd hp hnot2 hR2_val
  have hstep2 : ValPGe p E (((R ^ 2 - 1) / (2 : ℕ)) / (1 + (R - 1) / (2 : ℕ))) :=
    valPGe_div_one_add hp hhalf hstep1
  have hRadd_ne : R + 1 ≠ 0 := by
    have h2 := valPGe_div_one_add hp hhalf (valPGe_intCast_zero p hp 1)
    intro h0
    have hReq : R - 1 = -2 := by linarith
    rw [hReq] at hR1
    have hd := dvd_of_valPGe_int hp (show ValPGe p 1 ((-2 : ℤ) : ℚ) by simpa using hR1)
    rw [pow_one, Int.natCast_dvd] at hd
    exact hnot2 hd
  have hEq : ((R ^ 2 - 1) / (2 : ℕ)) / (1 + (R - 1) / (2 : ℕ)) = R - 1 := by
    push_cast
    have h1 : 1 + (R - 1) / 2 = (R + 1) / 2 := by ring
    rw [h1]
    field_simp [hRadd_ne]
    ring
  rwa [hEq] at hstep2

end A181069.RobertZuber

/-!
# The inverse-square residue sum used for A181069

Robert Osburn, Brundaban Sahu and Armin Straub, *Supercongruences for
sporadic sequences*, Lemma 2.2, equation (20), applied at exponent -2.
Multiplication by 2 permutes the residues, and 3 is a unit modulo the
prime power. Translation allows an arbitrary starting point for the block.
-/

namespace A181069.ReciprocalBlock

open Finset

private noncomputable def weight (N : ℕ) (x : ZMod N) : ZMod N := by
  classical
  exact if IsUnit x then x⁻¹ ^ 2 else 0

private theorem weight_unit {N : ℕ} (u : (ZMod N)ˣ) :
    weight N (u : ZMod N) = (↑(u⁻¹) : ZMod N) ^ 2 := by
  classical
  rw [weight, if_pos u.isUnit, ZMod.inv_coe_unit]

private theorem scale_weight {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    (u : ZMod N)^2 * weight N ((u : ZMod N) * x) = weight N x := by
  classical
  by_cases hx : IsUnit x
  · obtain ⟨v, rfl⟩ := hx
    change (u : ZMod N)^2 * weight N (↑(u*v) : ZMod N) = weight N (v : ZMod N)
    rw [weight_unit, weight_unit, ← mul_pow]
    have hc : u * (u * v)⁻¹ = v⁻¹ := by
      calc
        _ = (v⁻¹ * u⁻¹) * u := by rw [mul_inv_rev, mul_comm u]
        _ = v⁻¹ := by rw [mul_assoc, inv_mul_cancel, mul_one]
    exact congrArg (fun z : (ZMod N)ˣ => (z : ZMod N)^2) hc
  · have hux : ¬ IsUnit ((u : ZMod N) * x) := fun h => hx (isUnit_of_mul_isUnit_right h)
    simp [weight, hx, hux]

private theorem complete_sum (p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    [NeZero (p^s)] : (∑ x : ZMod (p^s), weight (p^s) x) = 0 := by
  have hsmall {a : ℕ} (ha : 0 < a) (hlt : a < p) : a.Coprime (p^s) :=
    ((hp.coprime_iff_not_dvd.mpr (fun hd => (Nat.not_le_of_lt hlt)
      (Nat.le_of_dvd ha hd))).symm).pow_right s
  let u := ZMod.unitOfCoprime 2 (hsmall (by decide) (by omega))
  let v := ZMod.unitOfCoprime 3 (hsmall (by decide) (by omega))
  have hu : (u : ZMod (p^s)) = 2 := by simp [u]
  have hv : (v : ZMod (p^s)) = 3 := by simp [v]
  let S := ∑ x : ZMod (p^s), weight (p^s) x
  have hperm : (∑ x : ZMod (p^s), weight (p^s) ((u : ZMod (p^s)) * x)) = S :=
    Equiv.sum_comp u.mulLeft (weight (p^s))
  have hmul : (2 : ZMod (p^s))^2 * S = S := calc
    _ = (u : ZMod (p^s))^2 *
        ∑ x : ZMod (p^s), weight (p^s) ((u : ZMod (p^s)) * x) := by rw [hperm, hu]
    _ = S := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => scale_weight u x)
  have hz : (3 : ZMod (p^s)) * S = 0 := by linear_combination hmul
  have hvz : (v : ZMod (p^s)) * S = 0 := by simpa only [hv] using hz
  change S = 0
  calc
    S = (↑(v⁻¹) : ZMod (p^s)) * ((v : ZMod (p^s)) * S) :=
      (v.inv_mul_cancel_left S).symm
    _ = 0 := by rw [hvz, mul_zero]

private def residueEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun j := (j.val : ZMod N)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv j := Fin.ext (ZMod.val_natCast_of_lt j.isLt)
  right_inv x := ZMod.natCast_zmod_val x

/-- Sum the inverse squares at offsets 0 through p^s-1, omitting indices
divisible by p. The starting index is arbitrary. -/
theorem inverse_squares_range (p s start : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) :
    (∑ i ∈ (range (p^s)).filter (fun i => ¬p ∣ start+i),
      (((start+i : ℕ) : ZMod (p^s))⁻¹)^2) = 0 := by
  classical
  letI : NeZero (p^s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Finset.sum_filter]
  calc
    _ = ∑ j ∈ range (p^s), weight (p^s) ((start+j : ℕ) : ZMod (p^s)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [weight, ZMod.isUnit_natCast_iff_not_dvd_pow hp hs]
    _ = ∑ j : Fin (p^s), weight (p^s) ((start+j.val : ℕ) : ZMod (p^s)) :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ x : ZMod (p^s), weight (p^s) x := by
      let e := (residueEquiv (p^s)).trans (Equiv.addLeft (start : ZMod (p^s)))
      calc
        _ = ∑ j : Fin (p^s), weight (p^s) (e j) := by
          apply Finset.sum_congr rfl
          intro j _
          change weight (p^s) ((start+j.val : ℕ) : ZMod (p^s)) =
            weight (p^s) ((start : ZMod (p^s)) + (j.val : ZMod (p^s)))
          rw [Nat.cast_add]
        _ = _ := Equiv.sum_comp e (weight (p^s))
    _ = 0 := complete_sum p s hp hp5

/-- The same congruence with the original integer as the summation index. -/
theorem inverse_squares_Ico (p s start : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) :
    (∑ j ∈ (Ico start (start+p^s)).filter (fun j => ¬p ∣ j),
      ((j : ZMod (p^s))⁻¹)^2) = 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel_left, Finset.sum_filter] using
    inverse_squares_range p s start hp hp5 hs

end A181069.ReciprocalBlock

/-!
# Prefixes of the unit inverse-square sum

Combine after A181069ReciprocalBlock. The modulus p^r is fixed throughout
the subsequent summation by parts. When p^s divides the endpoint, the
inverse-square partial sum vanishes after reduction to the smaller modulus p^s.
-/

namespace A181069.Prefix

open Finset

noncomputable def unitInvSq (p r j : ℕ) : ZMod (p ^ r) :=
  if p ∣ j then 0 else ((j : ZMod (p ^ r))⁻¹) ^ 2

noncomputable def partialSum (p r t : ℕ) : ZMod (p ^ r) :=
  ∑ i ∈ range t, unitInvSq p r (i + 1)

theorem map_unitInvSq (p r s j : ℕ) (hp : p.Prime) (hsr : s ≤ r) :
    ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s)) (unitInvSq p r j) =
      unitInvSq p s j := by
  let φ := ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s))
  change φ (unitInvSq p r j) = unitInvSq p s j
  by_cases hj : p ∣ j
  · simp [unitInvSq, hj]
  · have hur : IsUnit (j : ZMod (p ^ r)) :=
      (ZMod.isUnit_iff_coprime j (p ^ r)).mpr (hp.coprime_pow_of_not_dvd hj)
    have hus : IsUnit (j : ZMod (p ^ s)) :=
      (ZMod.isUnit_iff_coprime j (p ^ s)).mpr (hp.coprime_pow_of_not_dvd hj)
    have hmul : (j : ZMod (p ^ s)) * φ ((j : ZMod (p ^ r))⁻¹) = 1 := by
      simpa only [map_mul, map_natCast, map_one] using
        congrArg φ (ZMod.mul_inv_of_unit _ hur)
    have hinv : φ ((j : ZMod (p ^ r))⁻¹) = (j : ZMod (p ^ s))⁻¹ :=
      hus.mul_left_cancel (hmul.trans (ZMod.mul_inv_of_unit _ hus).symm)
    simp only [unitInvSq, if_neg hj, map_pow, hinv]

theorem map_prefix (p r s t : ℕ) (hp : p.Prime) (hsr : s ≤ r) :
    ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s)) (partialSum p r t) =
      partialSum p s t := by
  simp only [partialSum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact map_unitInvSq p r s (i + 1) hp hsr

private theorem complete_offset_block (p s a : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) : (∑ i ∈ range (p ^ s), unitInvSq p s (a + i)) = 0 := by
  classical
  have h := A181069.ReciprocalBlock.inverse_squares_Ico p s a hp hp5 hs
  rw [Finset.sum_filter, Finset.sum_Ico_eq_sum_range] at h
  calc
    _ = ∑ i ∈ range (p ^ s), if ¬p ∣ a + i then
        (((a + i : ℕ) : ZMod (p ^ s))⁻¹) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hd : p ∣ a + i <;> simp [unitInvSq, hd]
    _ = 0 := by simpa only [Nat.add_sub_cancel_left] using h

private theorem prefix_blocks (p s c : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) : partialSum p s (c * p ^ s) = 0 := by
  induction c with
  | zero => simp [partialSum]
  | succ c ih =>
    rw [Nat.succ_mul, partialSum, Finset.sum_range_add]
    change partialSum p s (c * p ^ s) +
      (∑ i ∈ range (p ^ s), unitInvSq p s (c * p ^ s + i + 1)) = 0
    rw [ih, zero_add]
    calc
      _ = ∑ i ∈ range (p ^ s), unitInvSq p s (c * p ^ s + 1 + i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show c * p ^ s + i + 1 = c * p ^ s + 1 + i by omega]
      _ = 0 := complete_offset_block p s (c * p ^ s + 1) hp hp5 hs

theorem prefix_dvd (p r t s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hsr : s ≤ r)
    (hst : p ^ s ∣ t) : (p : ZMod (p ^ r)) ^ s ∣ partialSum p r t := by
  by_cases hs : s = 0
  · simp [hs]
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  letI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let φ := ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s))
  let x := partialSum p r t
  have hz : partialSum p s t = 0 := by
    obtain ⟨m, hm⟩ := hst
    rw [hm, Nat.mul_comm (p ^ s) m]
    exact prefix_blocks p s m hp hp5 hspos
  have hproj : φ x = 0 := (map_prefix p r s t hp hsr).trans hz
  have hv : p ^ s ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff x.val (p ^ s)).mp
    have hmap : φ (x.val : ZMod (p ^ r)) = (x.val : ZMod (p ^ s)) := map_natCast _ _
    rw [← hmap, ZMod.natCast_zmod_val, hproj]
  obtain ⟨w, hw⟩ := hv
  refine ⟨(w : ZMod (p ^ r)), ?_⟩
  change x = (p : ZMod (p ^ r)) ^ s * (w : ZMod (p ^ r))
  calc
    x = (x.val : ZMod (p ^ r)) := (ZMod.natCast_zmod_val x).symm
    _ = (((p ^ s) * w : ℕ) : ZMod (p ^ r)) := by rw [hw]
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_pow]

end A181069.Prefix

/-!
Finite summation by parts for the unit-index contribution to A181069.
The auxiliary modules Adjacent and Prefix precede this one when assembling
the single project proof file.
-/

namespace A181069.Abel

open scoped BigOperators

def sumTo {R : Type*} [AddCommMonoid R] (f : ℕ → R) (t : ℕ) :=
  ∑ i ∈ Finset.range t, f (i + 1)

private theorem sumTo_succ {R : Type*} [AddCommMonoid R] (f : ℕ → R) (t : ℕ) :
    sumTo f (t+1) = sumTo f t + f (t+1) := Finset.sum_range_succ _ _

theorem discrete_abel {R : Type*} [CommRing R] (w f : ℕ → R) (n : ℕ) :
    sumTo (fun j => w j * f j) n +
      sumTo (fun j => (w (j+1)-w j) * sumTo f j) n =
        w (n+1) * sumTo f n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo_succ (fun j => w j * f j) n,
      sumTo_succ (fun j => (w (j+1)-w j) * sumTo f j) n,
      sumTo_succ f n]
    linear_combination ih

end A181069.Abel

namespace A098274

/-- Summands for the ordinary row and its predecessor, both extended through index N. -/
def term (b : Bool) (N j : ℕ) : ℕ :=
  if b then
    (N-1).choose j ^ 2 * (N+j-1).choose j * (N+2*j-1).choose (2*j)
  else
    N.choose j ^ 2 * (N+j).choose j * (N+2*j).choose (2*j)

/-- Integer weights after extracting N²/j² in the ordinary row, or N²/(2j²)
in its predecessor. Only positive j matters in the partial summation. -/
def weight (b : Bool) (N j : ℕ) : ℕ :=
  if b then
    (N-1).choose j ^ 2 * (N+j-1).choose (j-1) * (N+2*j-1).choose (2*j-1)
  else
    (N-1).choose (j-1) ^ 2 * (N+j).choose j * (N+2*j).choose (2*j)

end A098274

namespace A098274

theorem term_clear (b : Bool) (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (_hjN : j ≤ N) :
    ((if b then 2 else 1) * j^2) * term b N j = N^2 * weight b N j := by
  cases b with
  | false =>
    have h := Nat.add_one_mul_choose_eq (N-1) (j-1)
    rw [show N-1+1=N by omega, show j-1+1=j by omega] at h
    have hc : j * N.choose j = N * (N-1).choose (j-1) := by
      calc
        j * N.choose j = N.choose j * j := Nat.mul_comm _ _
        _ = _ := h.symm
    simp only [term, weight, Bool.false_eq_true, ↓reduceIte, one_mul]
    calc
      _ = (j * N.choose j)^2 * (N+j).choose j * (N+2*j).choose (2*j) := by ring
      _ = _ := by rw [hc]; ring
  | true =>
    have hshift (s : ℕ) (hs : 0 < s) :
        s * (N+s-1).choose s = N * (N+s-1).choose (s-1) := by
      have h := Nat.choose_succ_right_eq (N+s-1) (s-1)
      rw [show s-1+1=s by omega, show N+s-1-(s-1)=N by omega] at h
      calc
        s * (N+s-1).choose s = (N+s-1).choose s * s := Nat.mul_comm _ _
        _ = (N+s-1).choose (s-1) * N := h
        _ = _ := Nat.mul_comm _ _
    simp only [term, weight, Bool.true_eq, ↓reduceIte]
    calc
      _ = (N-1).choose j ^ 2 * (j * (N+j-1).choose j) *
          ((2*j) * (N+2*j-1).choose (2*j)) := by ring
      _ = _ := by
        rw [hshift j hj, hshift (2*j) (by omega)]
        ring

end A098274

namespace A098274

open Finset A181069.Prefix

theorem lift_divisor_of_zero (p a b : ℕ) (hp : p.Prime) (hab : a ≤ b)
    (x : ZMod (p^b)) (hx : ZMod.castHom (pow_dvd_pow p hab) (ZMod (p^a)) x = 0) :
    (p : ZMod (p^b))^a ∣ x := by
  letI : NeZero (p^b) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let φ := ZMod.castHom (pow_dvd_pow p hab) (ZMod (p^a))
  have hv : p^a ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff x.val (p^a)).mp
    have hmap : φ (x.val : ZMod (p^b)) = (x.val : ZMod (p^a)) := map_natCast _ _
    rw [← hmap, ZMod.natCast_zmod_val]
    exact hx
  obtain ⟨m,hm⟩ := hv
  refine ⟨(m : ZMod (p^b)), ?_⟩
  calc
    x = (x.val : ZMod (p^b)) := (ZMod.natCast_zmod_val x).symm
    _ = ((p^a*m : ℕ) : ZMod (p^b)) := by rw [hm]
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_pow]

private theorem odd_reflection (p s a b : ℕ) (hp : p.Prime) (hs : 0 < s)
    (hd : p^s ∣ a+b) : unitInvSq p s a = unitInvSq p s b := by
  let R := ZMod (p^s)
  have hpq : p ∣ p^s := by
    simpa only [pow_one] using pow_dvd_pow p (show 1 ≤ s by omega)
  have hab := dvd_trans hpq hd
  have hdvd : p ∣ a ↔ p ∣ b := by
    constructor
    · intro ha
      simpa using Nat.dvd_sub hab ha
    · intro hb
      simpa using Nat.dvd_sub hab hb
  by_cases ha : p ∣ a
  · simp [unitInvSq, ha, hdvd.mp ha]
  have hb : ¬p ∣ b := fun h => ha (hdvd.mpr h)
  have hz : (a:R)+(b:R)=0 := by
    simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (a+b) (p^s)).mpr hd
  have hneg : (a:R) = -(b:R) := eq_neg_of_add_eq_zero_left hz
  have hu : IsUnit (b:R) :=
    (ZMod.isUnit_iff_coprime b (p^s)).mpr (hp.coprime_pow_of_not_dvd hb)
  have hinv : (a:R)⁻¹ = -(b:R)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [hneg, neg_mul_neg, ZMod.mul_inv_of_unit _ hu]
  simp only [unitInvSq, if_neg ha, if_neg hb]
  rw [hinv]
  ring

private theorem partial_at_multiple (p s j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : p^s ∣ j) : partialSum p s j = 0 := by
  obtain ⟨w,hw⟩ := prefix_dvd p s j s hp hp5 le_rfl hd
  have hz : (p:ZMod (p^s))^s=0 := by
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (p^s) (p^s)).mpr dvd_rfl
  rw [hw, hz, zero_mul]

private theorem half_end_zero (p s j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs : 0 < s) (hd : p^s ∣ 2*j+1) : partialSum p s j = 0 := by
  let R := ZMod (p^s)
  let f : ℕ → R := unitInvSq p s
  have hpq : p ∣ p^s := by
    simpa only [pow_one] using pow_dvd_pow p (show 1 ≤ s by omega)
  have hlast : f (2*j+1) = 0 := by simp [f, unitInvSq, dvd_trans hpq hd]
  have hreflection :
      (∑ i ∈ range j, f (j+i+1)) = ∑ i ∈ range j, f (i+1) := by
    calc
      _ = ∑ i ∈ range j, (fun t => f (t+1)) (j-1-i) := by
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        apply odd_reflection p s _ _ hp hs
        simpa only [show j+i+1+(j-1-i+1)=2*j+1 by omega] using hd
      _ = _ := sum_range_reflect (fun t => f (t+1)) j
  have hfull := partial_at_multiple p s (2*j+1) hp hp5 hd
  change (∑ i ∈ range (2*j+1), f (i+1)) = 0 at hfull
  rw [sum_range_succ, hlast, add_zero, show 2*j=j+j by omega,
    sum_range_add, hreflection] at hfull
  have htwo : IsUnit (2:R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p^s)).mpr
    apply hp.coprime_pow_of_not_dvd
    intro hd'
    have := Nat.le_of_dvd (by decide : 0 < 2) hd'
    omega
  change (∑ i ∈ range j, f (i+1)) = 0
  apply htwo.mul_left_cancel
  rw [mul_zero, two_mul]
  exact hfull

/-- Full and half inverse-square sums vanish at all three possible jumps. -/
theorem partial_dvd_three (p r s j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hsr : s ≤ r) (hd : p^s ∣ j ∨ p^s ∣ j+1 ∨ p^s ∣ 2*j+1) :
    (p : ZMod (p^r))^s ∣ partialSum p r j := by
  by_cases hs : s = 0
  · simp [hs]
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  apply lift_divisor_of_zero p s r hp hsr
  rw [map_prefix p r s j hp hsr]
  rcases hd with hd | hd | hd
  · exact partial_at_multiple p s j hp hp5 hd
  · have hfull := partial_at_multiple p s (j+1) hp hp5 hd
    have hpq : p ∣ p^s := by
      simpa only [pow_one] using pow_dvd_pow p (show 1 ≤ s by omega)
    simpa only [partialSum, sum_range_succ, unitInvSq, if_pos (dvd_trans hpq hd),
      add_zero] using hfull
  · exact half_end_zero p s j hp hp5 hspos hd

end A098274

namespace A098274

def jump (p r j : ℕ) : ℕ :=
  min r (max (j.factorization p) (max ((j+1).factorization p) ((2*j+1).factorization p)))

private def rising (N t : ℕ) := (N+t).choose t

private theorem cancel_at {p r d t u : ℕ} (hp : p.Prime) (ht : 0 < t)
    (hd : d ≤ r - min (t.factorization p) r) (h : p^r ∣ t*u) :
    (u : ZMod (p^d)) = 0 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  apply dvd_trans (pow_dvd_pow p hd)
  by_cases hu : u=0
  · simp [hu]
  apply (hp.pow_dvd_iff_le_factorization hu).mpr
  have hv := (hp.pow_dvd_iff_le_factorization (mul_ne_zero ht.ne' hu)).mp h
  rw [Nat.factorization_mul ht.ne' hu, Finsupp.add_apply] at hv
  omega

private theorem rising_step (p r d N t : ℕ) (hp : p.Prime) (hdiv : p^r ∣ N)
    (ht : 0 < t) (hd : d ≤ r - min (t.factorization p) r) :
    (rising N t : ZMod (p^d)) = (rising N (t-1) : ZMod (p^d)) := by
  cases t with
  | zero => omega
  | succ t =>
    have he : (t+1) * (N+t).choose (t+1) = N * (N+t).choose t := by
      simpa only [mul_comm (t+1), mul_comm N, Nat.add_sub_cancel] using
        Nat.choose_succ_right_eq (N+t) t
    have hprod : p^r ∣ (t+1) * (N+t).choose (t+1) := by
      rw [he]
      exact dvd_mul_of_dvd_left hdiv _
    have hz := cancel_at hp ht hd hprod
    change (((N+(t+1)).choose (t+1) : ℕ) : ZMod (p^d)) =
      (((N+t).choose t : ℕ) : ZMod (p^d))
    rw [← Nat.add_assoc, Nat.choose_succ_succ', Nat.cast_add, hz, add_zero]

private theorem falling_square_step (p r d N t : ℕ) (hp : p.Prime) (hN : 0 < N)
    (hdiv : p^r ∣ N) (ht : 0 < t) (hd : d ≤ r - min (t.factorization p) r) :
    ((N-1).choose t : ZMod (p^d))^2 = ((N-1).choose (t-1) : ZMod (p^d))^2 := by
  have he : t * ((N-1).choose t + (N-1).choose (t-1)) = N * (N-1).choose (t-1) := by
    cases N with
    | zero => omega
    | succ m =>
      cases t with
      | zero => omega
      | succ i =>
        change (i+1) * (m.choose (i+1) + m.choose i) = (m+1)*m.choose i
        rw [add_comm (m.choose (i+1)) (m.choose i), ← Nat.choose_succ_succ']
        simpa only [mul_comm] using (Nat.add_one_mul_choose_eq m i).symm
  have hprod : p^r ∣ t * ((N-1).choose t + (N-1).choose (t-1)) := by
    rw [he]
    exact dvd_mul_of_dvd_left hdiv _
  have hz := cancel_at hp ht hd hprod
  rw [Nat.cast_add] at hz
  rw [eq_neg_of_add_eq_zero_left hz]
  ring

private theorem doubled_factor (p t : ℕ) (hp5 : 5 ≤ p) (ht : 0 < t) :
    (2*t).factorization p = t.factorization p := by
  rw [Nat.factorization_mul (by decide : 2 ≠ 0) ht.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_lt (show 2 < p by omega), zero_add]

private theorem weight_false (N j : ℕ) :
    weight false N j = (N-1).choose (j-1)^2 * rising N j * rising N (2*j) := rfl

private theorem weight_true (N j : ℕ) (hj : 0 < j) :
    weight true N j = (N-1).choose j^2 * rising N (j-1) * rising N (2*j-1) := by
  change (N-1).choose j ^ 2 * (N+j-1).choose (j-1) * (N+2*j-1).choose (2*j-1) =
    (N-1).choose j ^ 2 * (N+(j-1)).choose (j-1) * (N+(2*j-1)).choose (2*j-1)
  rw [show N+j-1=N+(j-1) by omega, show N+2*j-1=N+(2*j-1) by omega]

theorem adjacent_equal (p r N j : ℕ) (b : Bool) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^r ∣ N) (hj : 0 < j) :
    (weight b N (j+1) : ZMod (p^(r-jump p r j))) =
      (weight b N j : ZMod (p^(r-jump p r j))) := by
  let d := r-jump p r j
  have h1 : d ≤ r - min (j.factorization p) r := by dsimp [d,jump]; omega
  have h2 : d ≤ r - min ((j+1).factorization p) r := by dsimp [d,jump]; omega
  have h3 : d ≤ r - min ((2*j+1).factorization p) r := by dsimp [d,jump]; omega
  have h4 : d ≤ r - min ((2*j).factorization p) r := by rw [doubled_factor p j hp5 hj]; exact h1
  have h5 : d ≤ r - min ((2*(j+1)).factorization p) r := by
    rw [doubled_factor p (j+1) hp5 (by omega)]; exact h2
  have hr1 := rising_step p r d N j hp hdiv hj h1
  have hr2 := rising_step p r d N (j+1) hp hdiv (by omega) h2
  have hr3 := rising_step p r d N (2*j+1) hp hdiv (by omega) h3
  have hr4 := rising_step p r d N (2*j) hp hdiv (by omega) h4
  have hr5 := rising_step p r d N (2*(j+1)) hp hdiv (by omega) h5
  have hf1 := falling_square_step p r d N j hp hN hdiv hj h1
  have hf2 := falling_square_step p r d N (j+1) hp hN hdiv (by omega) h2
  simp only [Nat.add_sub_cancel] at hr2 hr3 hf2
  rw [show 2*(j+1)-1=2*j+1 by omega] at hr5
  cases b with
  | false =>
    simp only [weight_false, Nat.cast_mul, Nat.cast_pow, Nat.add_sub_cancel]
    rw [hf1, hr2, hr5, hr3]
  | true =>
    rw [weight_true N (j+1) (by omega), weight_true N j hj]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.add_sub_cancel]
    rw [show 2*(j+1)-1=2*j+1 by omega, hf2, hr1, hr3, hr4]

theorem jump_supported (p r j : ℕ) (hp : p.Prime) (hj : 0 < j) :
    p^(jump p r j) ∣ j ∨ p^(jump p r j) ∣ j+1 ∨ p^(jump p r j) ∣ 2*j+1 := by
  have h : jump p r j ≤ max (j.factorization p)
      (max ((j+1).factorization p) ((2*j+1).factorization p)) := min_le_right _ _
  rcases (le_max_iff.mp h) with h | h
  · exact Or.inl ((hp.pow_dvd_iff_le_factorization hj.ne').mpr h)
  rcases (le_max_iff.mp h) with h | h
  · exact Or.inr (Or.inl ((hp.pow_dvd_iff_le_factorization (by omega : j+1 ≠ 0)).mpr h))
  · exact Or.inr (Or.inr ((hp.pow_dvd_iff_le_factorization (by omega : 2*j+1 ≠ 0)).mpr h))

end A098274

/-!
# Both A098274 rows at indices divisible by the prime

This component follows the common Robert–Zuber implementation by @TheWaler
(project PR 5983), the A098274 summand definitions, and the cleared weight
identity. All three binomial factors scale by the same respective unit
ratios in the ordinary and predecessor rows.
-/

namespace A098274

open A181069.RobertZuber

private def entry (b : Bool) (A j : ℕ) : ℕ :=
  if b then (A-1).choose j else A.choose j

private def ratio (p a c : ℕ) : ℚ := H p (a+c) / (H p a * H p c)

private theorem ratio_bound {p a c x y z : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : p^x ∣ a) (hc : p^y ∣ c) (hs : p^z ∣ a+c) :
    ValPGe p (3+x+y+z) (ratio p a c - 1) := by
  have h0 : H p 0 = 1 := by simp [H]
  by_cases h : a = 0
  · subst a
    rw [ratio, zero_add, h0, one_mul, div_self (H_ne_zero hp _), sub_self]
    exact valPGe_zero p hp _
  by_cases h' : c = 0
  · subst c
    rw [ratio, add_zero, h0, mul_one, div_self (H_ne_zero hp _), sub_self]
    exact valPGe_zero p hp _
  letI : Fact p.Prime := ⟨hp⟩
  have hx := (padicValNat_dvd_iff_le h).mp ha
  have hy := (padicValNat_dvd_iff_le h').mp hc
  have hz := (padicValNat_dvd_iff_le (show a+c ≠ 0 by omega)).mp hs
  exact valPGe_mono (by omega) (robert_zuber_ratio hp (by omega) a c (by omega) (by omega))

private theorem shift_weight (A j : ℕ) (hA : 0 < A) :
    (A : ℚ) * ((A-1).choose j : ℚ) = ((A-j : ℕ) : ℚ) * (A.choose j : ℚ) := by
  have hn := Nat.choose_mul_succ_eq (A-1) j
  rw [Nat.sub_add_cancel hA] at hn
  have h : A * (A-1).choose j = (A-j) * A.choose j := by
    simpa only [Nat.mul_comm] using hn
  exact_mod_cast h

private theorem scale_entry (b : Bool) (p A j : ℕ) (hp : p.Prime)
    (hA : 0 < A) (hj : j ≤ A) :
    (entry b (p*A) (p*j) : ℚ) = (entry b A j : ℚ) * ratio p j (A-j) := by
  have hc : ((p*A).choose (p*j) : ℚ) = (A.choose j : ℚ) * ratio p j (A-j) := by
    have hn := mul_ne_zero (H_ne_zero hp j) (H_ne_zero hp (A-j))
    rw [ratio, show j+(A-j) = A by omega, ← mul_div_assoc, eq_div_iff hn]
    exact choose_pn_pk_eq p A j hp.one_le hj
  cases b with
  | false => exact hc
  | true =>
    change ((p*A-1).choose (p*j) : ℚ) = ((A-1).choose j : ℚ) * _
    have hu := shift_weight (p*A) (p*j) (Nat.mul_pos hp.pos hA)
    rw [hc, ← Nat.mul_sub_left_distrib] at hu
    simp only [Nat.cast_mul] at hu
    have hl := shift_weight A j hA
    have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hAQ : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA)
    apply mul_left_cancel₀ (mul_ne_zero hpQ hAQ)
    linear_combination hu - (p:ℚ) * ratio p j (A-j) * hl

private theorem product_close {p e : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : ValPGe p e (x-1)) (hy : ValPGe p e (y-1)) :
    ValPGe p e (x*y-1) := by
  have h1 : ValPGe p 0 (1:ℚ) := by simpa using valPGe_intCast_zero p hp 1
  have hy0 : ValPGe p 0 y := by
    simpa using (valPGe_add hp (valPGe_mono (Nat.zero_le e) hy) h1)
  have hxy : ValPGe p e ((x-1)*y) := by
    simpa only [Nat.add_zero] using valPGe_mul hp hx hy0
  rw [show x*y-1 = (x-1)*y+(y-1) by ring]
  exact valPGe_add hp hxy hy

private theorem cast_term_entries (b : Bool) (A j : ℕ) :
    (term b A j : ℚ) = (entry b A j : ℚ)^2 *
      (entry b (A+j) j : ℚ) * (entry b (A+2*j) (2*j) : ℚ) := by
  cases b <;> simp [term, entry]

private theorem term_scale (b : Bool) (p A j : ℕ) (hp : p.Prime)
    (hA : 0 < A) (hj : j ≤ A) :
    (term b (p*A) (p*j) : ℚ) = (term b A j : ℚ) *
      (ratio p j (A-j) * ratio p j (A-j) * ratio p j A * ratio p (2*j) A) := by
  have h1 := scale_entry b p A j hp hA hj
  have h2 := scale_entry b p (A+j) j hp (by omega) (by omega)
  have h3 := scale_entry b p (A+2*j) (2*j) hp (by omega) (by omega)
  rw [show A+j-j=A by omega] at h2
  rw [show A+2*j-2*j=A by omega] at h3
  rw [cast_term_entries b (p*A) (p*j), cast_term_entries b A j,
    show 2*(p*j) = p*(2*j) by ring, show p*A+p*j=p*(A+j) by ring,
    show p*A+p*(2*j)=p*(A+2*j) by ring, h1, h2, h3]
  ring

private theorem term_valuation (b : Bool) (p A j v : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hA : 0 < A) (hj : 0 < j) (hjA : j ≤ A) (hdiv : p^v ∣ A) :
    ValPGe p (2*(v - min v (padicValNat p j))) (term b A j : ℚ) := by
  letI : Fact p.Prime := ⟨hp⟩
  let c : ℕ := if b then 2 else 1
  have hc : 0 < c := by cases b <;> norm_num [c]
  have hsmall : ¬p ∣ c := by
    intro h
    have hle := Nat.le_of_dvd hc h
    have : c ≤ 2 := by cases b <;> norm_num [c]
    omega
  by_cases hzero : term b A j = 0
  · rw [hzero, Nat.cast_zero]
    exact valPGe_zero p hp _
  have hsq : p^(2*v) ∣ (c*j^2)*term b A j := by
    change p^(2*v) ∣ ((if b then 2 else 1)*j^2)*term b A j
    rw [term_clear b A j hA hj hjA, show 2*v = v*2 by omega, pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hdiv 2) _
  have hj2 : j^2 ≠ 0 := pow_ne_zero 2 hj.ne'
  have hcv : c*j^2 ≠ 0 := Nat.mul_ne_zero hc.ne' hj2
  have hval := (padicValNat_dvd_iff_le (Nat.mul_ne_zero hcv hzero)).mp hsq
  rw [padicValNat.mul hcv hzero, padicValNat.mul hc.ne' hj2,
    padicValNat.eq_zero_of_not_dvd hsmall, padicValNat.pow, zero_add] at hval
  exact valPGe_mono (by omega) (valPGe_natCast_padicValNat hp (term b A j))

theorem aligned_transfer (b : Bool) (p M r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 0 < M) (hr : 0 < r) (hdiv : p^(r-1) ∣ M) (i : ℕ) (hi : i ≤ M) :
    (term b (p*M) (p*i) : ZMod (p^(3*r))) = (term b M i : ZMod (p^(3*r))) := by
  by_cases hi0 : i = 0
  · subst i
    cases b <;> simp [term]
  let v := r-1
  let t := min v (padicValNat p i)
  have ht : t ≤ v := min_le_left _ _
  have hti : t ≤ padicValNat p i := min_le_right _ _
  have hmt : p^t ∣ M := (pow_dvd_pow p ht).trans hdiv
  have hit : p^t ∣ i := (pow_dvd_pow p hti).trans pow_padicValNat_dvd
  have ht2 : p^t ∣ 2*i := dvd_mul_of_dvd_right hit 2
  let E := 3+v+2*t
  have h1 : ValPGe p E (ratio p i (M-i) - 1) := by
    have h := ratio_bound hp hp5 hit (Nat.dvd_sub hmt hit)
      (show p^v ∣ i+(M-i) by rwa [show i+(M-i)=M by omega])
    simpa only [E, show 3+v+2*t = 3+t+t+v by omega] using h
  have h2 : ValPGe p E (ratio p i M - 1) := by
    have h := ratio_bound hp hp5 hit hdiv (dvd_add hit hmt)
    simpa only [E, v, show 3+(r-1)+2*t = 3+t+(r-1)+t by omega] using h
  have h3 : ValPGe p E (ratio p (2*i) M - 1) := by
    have h := ratio_bound hp hp5 ht2 hdiv (dvd_add ht2 hmt)
    simpa only [E, v, show 3+(r-1)+2*t = 3+t+(r-1)+t by omega] using h
  have hrat := product_close hp (product_close hp (product_close hp h1 h1) h2) h3
  have hbase := term_valuation b p M i v hp hp5 hM (by omega) hi hdiv
  have hscale := term_scale b p M i hp hM hi
  have hdiff : ValPGe p (3*r)
      (((term b (p*M) (p*i) : ℤ) - (term b M i : ℤ) : ℤ) : ℚ) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hscale]
    rw [show (term b M i : ℚ) *
      (ratio p i (M-i) * ratio p i (M-i) * ratio p i M * ratio p (2*i) M) -
      (term b M i : ℚ) = (term b M i : ℚ) *
      (ratio p i (M-i) * ratio p i (M-i) * ratio p i M * ratio p (2*i) M - 1) by ring]
    have hvr : v+1 = r := by dsimp [v]; omega
    have hv : 3*r ≤ 2*(v-t)+E := by dsimp [E]; omega
    exact valPGe_mono hv (valPGe_mul hp hbase hrat)
  have hd := dvd_of_valPGe_int hp hdiff
  apply sub_eq_zero.mp
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  simpa only [Int.cast_sub, Int.cast_natCast] using hc

end A098274

namespace A098274

open Finset A181069.Prefix A181069.Abel

private theorem weighted_zero (p r N : ℕ) (b : Bool) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^r ∣ N) :
    (∑ i ∈ range N, (weight b N (i+1) : ZMod (p^r)) * unitInvSq p r (i+1)) = 0 := by
  let R := ZMod (p^r)
  let w : ℕ → R := fun j => weight b N j
  let f : ℕ → R := unitInvSq p r
  have hzero : (p:R)^r = 0 := by
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (p^r) (p^r)).mpr dvd_rfl
  have hlast : sumTo f N = 0 := by
    obtain ⟨c,hc⟩ := prefix_dvd p r N r hp hp5 le_rfl hdiv
    change partialSum p r N = 0
    rw [hc, hzero, zero_mul]
  have hinterior : sumTo (fun j => (w (j+1)-w j) * sumTo f j) N = 0 := by
    apply sum_eq_zero
    intro i hi
    let j := i+1
    have hj : 0 < j := Nat.succ_pos i
    let s := jump p r j
    have hs : s ≤ r := min_le_left _ _
    let d := r-s
    have hdr : d ≤ r := Nat.sub_le _ _
    let ψ := ZMod.castHom (pow_dvd_pow p hdr) (ZMod (p^d))
    have hdiff : ψ (w (j+1)-w j) = 0 := by
      change ψ ((weight b N (j+1) : R)-(weight b N j : R))=0
      rw [map_sub, map_natCast, map_natCast, adjacent_equal p r N j b hp hp5 hN hdiv hj,
        sub_self]
    obtain ⟨a,ha⟩ := lift_divisor_of_zero p d r hp hdr (w (j+1)-w j) hdiff
    obtain ⟨c,hc⟩ := partial_dvd_three p r s j hp hp5 hs (jump_supported p r j hp hj)
    change (w (j+1)-w j) * partialSum p r j = 0
    rw [ha,hc]
    calc
      (p:R)^d * a * ((p:R)^s * c) = (p:R)^(d+s) * (a*c) := by rw [pow_add]; ring
      _ = 0 := by rw [show d+s=r by dsimp [d]; omega, hzero, zero_mul]
  have h := discrete_abel w f N
  rw [hinterior, add_zero, hlast, mul_zero] at h
  exact h

theorem off_grid (p r N : ℕ) (b : Bool) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hN : 0 < N) (hdiv : p^r ∣ N) :
    (∑ j ∈ (range (N+1)).filter (fun j => ¬p ∣ j), (term b N j : ZMod (p^(3*r)))) = 0 := by
  classical
  let U := ZMod (p^(3*r))
  let L := ZMod (p^r)
  let hru : r ≤ 3*r := by omega
  let φ := ZMod.castHom (pow_dvd_pow p hru) L
  let F : ℕ → U := fun j => (weight b N j : U) * unitInvSq p (3*r) j
  let X : U := ∑ i ∈ range N, F (i+1)
  let c : ℕ := if b then 2 else 1
  have hmap : φ X = 0 := by
    change φ (∑ i ∈ range N, F (i+1)) = 0
    rw [map_sum]
    calc
      (∑ i ∈ range N, φ (F (i+1))) =
          ∑ i ∈ range N, (weight b N (i+1) : L) * unitInvSq p r (i+1) := by
        apply sum_congr rfl
        intro i _
        dsimp only [F]
        rw [map_mul, map_natCast]
        exact congrArg ((weight b N (i+1) : L) * ·)
          (map_unitInvSq p (3*r) r (i+1) hp hru)
      _ = 0 := weighted_zero p r N b hp hp5 hN hdiv
  obtain ⟨z,hz⟩ := lift_divisor_of_zero p r (3*r) hp hru X hmap
  have vanish : (N:U)^2 * X = 0 := by
    obtain ⟨m,hm⟩ := hdiv
    have hmU : (N:U) = (p:U)^r * (m:U) := by
      calc
        (N:U) = ((p^r*m : ℕ) : U) := congrArg (fun n : ℕ => (n:U)) hm
        _ = (p:U)^r * (m:U) := by rw [Nat.cast_mul, Nat.cast_pow]
    have hzero : (p:U)^(3*r)=0 := by
      simpa only [Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (p^(3*r)) (p^(3*r))).mpr dvd_rfl
    have cubePower (x : U) : x^(3*r) = x^r*x^r*x^r := by
      calc
        x^(3*r) = x^((r+r)+r) := congrArg (fun e : ℕ => x^e) (show 3*r=(r+r)+r by omega)
        _ = x^r*x^r*x^r := by rw [pow_add, pow_add]
    calc
      (N:U)^2 * X = (p:U)^(3*r) * ((m:U)^2*z) := by
        rw [hmU, hz, cubePower (p:U)]
        ring
      _ = 0 := by rw [hzero,zero_mul]
  have hterm (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) (hjp : ¬p ∣ j) :
      (c:U) * (term b N j : U) = (N:U)^2 * F j := by
    have he := congrArg (fun a : ℕ => (a:U)) (term_clear b N j hN hj hjN)
    change (((c * j^2) * term b N j : ℕ) : U) = ((N^2 * weight b N j : ℕ) : U) at he
    have heU : (c:U) * (j:U)^2 * (term b N j:U) =
        (N:U)^2 * (weight b N j:U) := by
      calc
        _ = (((c * j^2) * term b N j : ℕ) : U) := by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
        _ = ((N^2 * weight b N j : ℕ) : U) := he
        _ = _ := by rw [Nat.cast_mul, Nat.cast_pow]
    have hjunit : IsUnit (j:U) :=
      (ZMod.isUnit_iff_coprime j (p^(3*r))).mpr (hp.coprime_pow_of_not_dvd hjp)
    calc
      (c:U) * (term b N j : U) =
          ((c:U) * (term b N j:U)) * ((j:U)*(j:U)⁻¹)^2 := by
            rw [ZMod.mul_inv_of_unit _ hjunit, one_pow, mul_one]
      _ = ((c:U) * (j:U)^2 * (term b N j:U)) * ((j:U)⁻¹)^2 := by ring
      _ = (N:U)^2 * F j := by
        rw [heU]
        simp only [F, unitInvSq, if_neg hjp]
        ring
  have hF0 : F 0 = 0 := by simp [F, unitInvSq]
  have hfull : (∑ j ∈ range (N+1), F j) = X := by
    simpa only [X, hF0, add_zero, zero_add] using Finset.sum_range_succ' F N
  have hc : IsUnit (c:U) := by
    cases b with
    | false => simp [c]
    | true =>
      change IsUnit (2:U)
      apply (ZMod.isUnit_iff_coprime 2 (p^(3*r))).mpr
      apply hp.coprime_pow_of_not_dvd
      intro hd
      have := Nat.le_of_dvd (by decide : 0 < 2) hd
      omega
  apply hc.mul_left_cancel
  rw [mul_zero, ← vanish, ← hfull, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
  apply sum_congr rfl
  intro j hj
  by_cases hjp : p ∣ j
  · simp [hjp,F,unitInvSq]
  · have hjpos : 0 < j := by
      by_contra! h
      exact hjp (by rw [show j = 0 by omega]; exact dvd_zero _)
    have hjN : j ≤ N := by have := mem_range.mp hj; omega
    simpa only [if_pos hjp] using hterm j hjpos hjN hjp

end A098274

namespace A098274

open Finset
open scoped BigOperators

/-- Both rows can be summed over `0, …, N`; the extra term of the shifted row is zero. -/
theorem row_as_terms (b : Bool) (N : ℕ) (hN : 0 < N) :
    OMA.S_oeis_a098274.a (if b then N-1 else N) =
      ∑ j ∈ range (N+1), term b N j := by
  have hsym (n j : ℕ) : (n+j).choose n = (n+j).choose j := by
    exact Nat.choose_symm_of_eq_add rfl
  cases b with
  | false =>
    change (∑ j ∈ range (N+1), N.choose j ^ 2 * (N+j).choose N * (N+2*j).choose N) =
      ∑ j ∈ range (N+1), N.choose j ^ 2 * (N+j).choose j * (N+2*j).choose (2*j)
    exact sum_congr rfl fun j _ => by rw [hsym N j, hsym N (2*j)]
  | true =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    change (∑ j ∈ range (m+1), m.choose j ^ 2 * (m+j).choose m * (m+2*j).choose m) =
      ∑ j ∈ range ((m+1)+1), term true (m+1) j
    have hz : term true (m+1) (m+1) = 0 := by
      simp [term, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m)]
    rw [sum_range_succ (fun j => term true (m+1) j) (m+1), hz, add_zero]
    exact sum_congr rfl fun j _ => by
      have h1 : m+1+j-1 = m+j := by omega
      have h2 : m+1+2*j-1 = m+2*j := by omega
      simp [term, h1, h2, hsym m j, hsym m (2*j)]

theorem row_of_split (p r M : ℕ) (b : Bool) (hp : p.Prime) (hM : 0 < M)
    (aligned : ∀ i ≤ M, (term b (p*M) (p*i) : ZMod (p^(3*r))) =
      (term b M i : ZMod (p^(3*r))))
    (off : (∑ j ∈ (range (p*M+1)).filter (fun j => ¬p ∣ j),
      (term b (p*M) j : ZMod (p^(3*r)))) = 0) :
    OMA.S_oeis_a098274.a (if b then p*M-1 else p*M) ≡
      OMA.S_oeis_a098274.a (if b then M-1 else M) [MOD p^(3*r)] := by
  classical
  let q := p^(3*r)
  let f : ℕ → ZMod q := fun j => term b (p*M) j
  let T := (range (p*M+1)).filter (fun j => p ∣ j)
  have hs : T = (range (M+1)).image (fun i => p*i) := by
    ext j
    simp only [T, mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨h, i, rfl⟩
      have hi := Nat.le_of_mul_le_mul_left (show p*i ≤ p*M by omega) hp.pos
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, h, rfl⟩
      have hj := Nat.mul_le_mul_left p (show i ≤ M by omega)
      exact ⟨by omega, ⟨i, rfl⟩⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ q).mp
  rw [row_as_terms b (p*M) (Nat.mul_pos hp.pos hM), row_as_terms b M hM]
  push_cast
  change (∑ j ∈ range (p*M+1), f j) = ∑ i ∈ range (M+1), (term b M i : ZMod q)
  calc
    _ = ∑ j ∈ T, f j := by
      have hh := sum_filter_add_sum_filter_not (range (p*M+1)) (fun j => p ∣ j) f
      have hzero : (∑ j ∈ (range (p*M+1)).filter (fun j => ¬p ∣ j), f j) = 0 := off
      rw [hzero, add_zero] at hh
      exact hh.symm
    _ = _ := by
      rw [hs, sum_image]
      · exact sum_congr rfl fun i hi => aligned i (by simpa using hi)
      · intro i _ j _ h
        exact Nat.eq_of_mul_eq_mul_left hp.pos h

end A098274

theorem OMA.solution : type_of% @OMA.S_oeis_a098274.main := by
  intro p n r hp hp5 hn hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let M := n * p^k
  have hM : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hlower : p^k ∣ M := ⟨n, by dsimp [M]; ring⟩
  have hupper : n * p^(k+1) = p*M := by rw [pow_succ]; dsimp [M]; ring
  have hd : p^(k+1) ∣ p*M := ⟨n, by rw [pow_succ]; dsimp [M]; ring⟩
  have rows (b : Bool) := A098274.row_of_split p (k+1) M b hp hM
    (A098274.aligned_transfer b p M (k+1) hp hp5 hM (by omega) hlower)
    (A098274.off_grid p (k+1) (p*M) b hp hp5 (Nat.mul_pos hp.pos hM) hd)
  change OMA.S_oeis_a098274.a (n * p^(k+1)) ≡ OMA.S_oeis_a098274.a M [MOD p^(3*(k+1))] ∧
    OMA.S_oeis_a098274.a (n * p^(k+1)-1) ≡ OMA.S_oeis_a098274.a (M-1) [MOD p^(3*(k+1))]
  rw [hupper]
  exact ⟨rows false, rows true⟩

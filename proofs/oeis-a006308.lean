import OMAStatements.S_oeis_a006308

/-!
# The period-polynomial coefficient in A006308

The first two power sums of the Gaussian periods determine the coefficient.
Orthogonality reduces the second moment to pairing opposite powers modulo p.
The cubic residue sum follows by pairing each nonzero input with its negative.

Michael Somos conjectured the identities in the OEIS entry. Sean A. Irvine
supplied the period-polynomial definition. Stephan Ramon Garcia and Bob Lutz,
“A supercharacter approach to Heilbronn sums”, equations (3.5), (3.6), and
(3.8), previously established the two moments and the resulting pairwise
product sum for the same periods, indexed by cosets. The proof below derives
the moments directly in Irvine's indexing. https://arxiv.org/abs/1312.1034

Credit: @dwilfand-sys (Lean formalization by Codex)
Source: https://oeis.org/A006308
-/

namespace OMA.PeriodGroup

open Finset

-- Raising two congruent integers to the p-th power gains one power of p.
lemma liftPower (p : ℕ) (a b : ℤ) (h : (a : ZMod p) = (b : ZMod p)) :
    (a : ZMod (p ^ 2)) ^ p = (b : ZMod (p ^ 2)) ^ p := by
  have hd : (p : ℤ) ∣ b - a :=
    ((ZMod.intCast_eq_intCast_iff a b p).mp h).dvd
  have hs := mul_dvd_mul (dvd_geom_sum₂_self (n := p) (x := b) (y := a) hd) hd
  have hl : a ^ p ≡ b ^ p [ZMOD (↑(p ^ 2 : ℕ) : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨c, hc⟩ := hs
    refine ⟨c, ?_⟩
    have hcast : ((p^2 : ℕ) : ℤ) = (p:ℤ)*(p:ℤ) :=
      (congrArg (fun n : ℕ => (n:ℤ)) (pow_two p)).trans (Nat.cast_mul p p)
    rw [hcast]
    simpa only [geom_sum₂_mul] using hc
  simpa only [Int.cast_pow] using (ZMod.intCast_eq_intCast_iff _ _ _).mpr hl

-- A generator mod p² remains a generator mod p.
lemma primitiveModPrime (p g : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    IsPrimitiveRoot (g : ZMod p) (p - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hg₂ : IsPrimitiveRoot (g : ZMod (p ^ 2)) (p * (p - 1)) :=
    IsPrimitiveRoot.iff_orderOf.mpr hg
  have hunit := hg₂.isUnit (Nat.mul_ne_zero hp.ne_zero (by omega))
  let π := ZMod.castHom (show p ∣ p ^ 2 from ⟨p, pow_two p⟩) (ZMod p)
  have hgp : IsUnit (g : ZMod p) := by simpa [π] using hunit.map π
  refine ⟨ZMod.pow_card_sub_one_eq_one hgp.ne_zero, ?_⟩
  intro d hd
  have hl := liftPower p ((g : ℤ) ^ d) 1 (by simpa using hd)
  have he : (g : ZMod (p ^ 2)) ^ (p * d) = 1 := by
    rw [Nat.mul_comm p d, pow_mul]
    simpa using hl
  exact Nat.dvd_of_mul_dvd_mul_left hp.pos ((hg₂.pow_eq_one_iff_dvd _).mp he)

lemma exponentUnits (p g : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    ∀ j ∈ range (p - 1), ¬ p ∣ (g ^ p) ^ j := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := (primitiveModPrime p g hp hp2 hg).isUnit (by omega)
  intro j _ hd
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simp only [Nat.cast_pow] at hz
  exact ((h.pow p).pow j).ne_zero hz

lemma oppositeExponents (p g : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hg : orderOf (g : ZMod (p ^ 2)) = p * (p - 1)) :
    ∀ j ∈ range (p - 1), ∃ t ∈ range (p - 1),
      p ^ 2 ∣ (g ^ p) ^ j + (g ^ p) ^ t ∧
      ∀ l ∈ range (p - 1), l ≠ t → ¬ p ∣ (g ^ p) ^ j + (g ^ p) ^ l := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p - 1) := ⟨by omega⟩
  have h := primitiveModPrime p g hp hp2 hg
  have hgp : (g : ZMod p) ≠ 0 := (h.isUnit (by omega)).ne_zero
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  intro j _
  have hn : (-(g : ZMod p) ^ j) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr (pow_ne_zero j hgp))
  obtain ⟨t, ht, he⟩ := h.eq_pow_of_pow_eq_one hn
  refine ⟨t, mem_range.mpr ht, ?_, ?_⟩
  · have hl := liftPower p ((g : ℤ) ^ t) (-((g : ℤ) ^ j)) (by simpa using he)
    have hz : ((g : ZMod (p ^ 2)) ^ t) ^ p = -(((g : ZMod (p ^ 2)) ^ j) ^ p) := by
      simpa only [Int.cast_pow, Int.cast_natCast, Int.cast_neg, ho.neg_pow] using hl
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_add, Nat.cast_pow, pow_right_comm (g : ZMod (p ^ 2)) p j,
      pow_right_comm (g : ZMod (p ^ 2)) p t, hz, add_neg_cancel]
  · intro l hl hlt hd
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    simp only [Nat.cast_add, Nat.cast_pow, ZMod.pow_card] at hz
    apply hlt
    apply h.pow_inj (mem_range.mp hl) ht
    calc
      (g : ZMod p) ^ l = -(g : ZMod p) ^ j := by linear_combination hz
      _ = (g : ZMod p) ^ t := he.symm

end OMA.PeriodGroup

namespace OMA.PeriodMoments

open Finset

lemma progressionZero {p : ℕ} (hp : 0 < p) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p ^ 2)) (q s : ℕ) (hs : ¬ p ∣ s) :
    (∑ k ∈ range p, ζ ^ ((q + k * p) * s)) = 0 := by
  let r := ζ ^ (p * s)
  have hr : r ≠ 1 := by
    intro he
    have hd := (hζ.pow_eq_one_iff_dvd (p * s)).mp he
    rw [pow_two] at hd
    exact hs (Nat.dvd_of_mul_dvd_mul_left hp hd)
  have hrp : r ^ p = 1 := by
    change (ζ ^ (p * s)) ^ p = 1
    rw [← pow_mul]
    apply (hζ.pow_eq_one_iff_dvd _).2
    exact ⟨s, by ring⟩
  have hgeom := geom_sum_mul r p
  rw [hrp, sub_self] at hgeom
  have hz : (∑ k ∈ range p, r ^ k) = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hr)
  calc
    _ = ∑ k ∈ range p, ζ ^ (q * s) * r ^ k := by
      apply sum_congr rfl
      intro k _
      dsimp [r]
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ = _ := by rw [← mul_sum, hz, mul_zero]

lemma progressionFull {p : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (q s : ℕ) (hs : p ^ 2 ∣ s) :
    (∑ k ∈ range p, ζ ^ ((q + k * p) * s)) = (p : ℂ) := by
  have he (k : ℕ) : ζ ^ ((q + k * p) * s) = 1 := by
    apply (hζ.pow_eq_one_iff_dvd _).2
    obtain ⟨u, hu⟩ := hs
    exact ⟨(q + k * p) * u, by rw [hu]; ring⟩
  simp [he]

noncomputable def period (p q : ℕ) (ζ : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range (p - 1), ζ ^ ((q + k * p) * q ^ j)

lemma firstMoment {p : ℕ} (hp : 0 < p) (q : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (hunit : ∀ j ∈ range (p - 1), ¬ p ∣ q ^ j) :
    (∑ k ∈ range p, period p q ζ k) = 0 := by
  unfold period
  rw [sum_comm]
  exact sum_eq_zero fun j hj => progressionZero hp hζ q _ (hunit j hj)

lemma secondMoment {p : ℕ} (hp : 0 < p) (q : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (hopposite : ∀ j ∈ range (p - 1), ∃ t ∈ range (p - 1),
      p ^ 2 ∣ q ^ j + q ^ t ∧
      ∀ l ∈ range (p - 1), l ≠ t → ¬ p ∣ q ^ j + q ^ l) :
    (∑ k ∈ range p, (period p q ζ k) ^ 2) = ((p - 1 : ℕ) : ℂ) * p := by
  let T := range (p - 1)
  let A (k j l : ℕ) := ζ ^ ((q + k * p) * (q ^ j + q ^ l))
  calc
    _ = ∑ k ∈ range p, ∑ j ∈ T, ∑ l ∈ T, A k j l := by
      simp only [period, T, A, pow_two, sum_mul, mul_sum, Nat.mul_add, pow_add]
      refine sum_congr rfl fun _ _ => ?_
      refine sum_congr rfl fun _ _ => ?_
      refine sum_congr rfl fun _ _ => ?_
      exact mul_comm _ _
    _ = ∑ j ∈ T, ∑ k ∈ range p, ∑ l ∈ T, A k j l := sum_comm
    _ = ∑ j ∈ T, ∑ l ∈ T, ∑ k ∈ range p, A k j l :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ j ∈ T, (p : ℂ) := by
      apply sum_congr rfl
      intro j hj
      obtain ⟨t, ht, htFull, hrest⟩ := hopposite j hj
      rw [sum_eq_single t]
      · exact progressionFull hζ q _ htFull
      · intro l hl hlt
        exact progressionZero hp hζ q _ (hrest l hl hlt)
      · intro h
        exact (h ht).elim
    _ = _ := by simp [T, nsmul_eq_mul]

end OMA.PeriodMoments

open Polynomial

namespace OMA.CyclotomicPeriods

/-- Multiplying by `X²` lets the second-coefficient formula include the empty and
singleton products in the same induction. -/
lemma twice_shifted_coefficient {ι : Type*} (s : Finset ι) (h : ι → ℂ) :
    2 * ((∏ i ∈ s, (X - C (h i))) * X ^ 2).coeff s.card =
      (∑ i ∈ s, h i) ^ 2 - ∑ i ∈ s, (h i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_X_pow]
  | @insert a s ha ih =>
    have hprev :
        ((∏ i ∈ s, (X - C (h i))) * X ^ 2).coeff (s.card + 1) =
          -∑ i ∈ s, h i := by
      by_cases hs : s.card = 0
      · have he : s = ∅ := Finset.card_eq_zero.mp hs
        subst s
        simp [Polynomial.coeff_X_pow]
      · have hpos : 0 < s.card := Nat.pos_of_ne_zero hs
        rw [Polynomial.coeff_mul_X_pow', if_pos (by omega : 2 ≤ s.card + 1),
          show s.card + 1 - 2 = s.card - 1 by omega]
        exact Polynomial.prod_X_sub_C_coeff_card_pred s h hpos
    rw [Finset.card_insert_of_notMem ha, Finset.prod_insert ha, mul_assoc,
      Polynomial.coeff_X_sub_C_mul, hprev, Finset.sum_insert ha, Finset.sum_insert ha]
    linear_combination ih

end OMA.CyclotomicPeriods

namespace OMA.CyclotomicPeriods

open Finset Polynomial
open OMA.S_oeis_a006308

lemma period_root_is_primitive {p : ℕ} (hp : 0 < p) :
    IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ) ^ 2))
      (p ^ 2) := by
  simpa only [Nat.cast_pow] using
    Complex.isPrimitiveRoot_exp (p ^ 2) (pow_ne_zero _ hp.ne')

lemma triangular_cast {p : ℕ} (hp : 1 ≤ p) :
    ((p * (p - 1) / 2 : ℕ) : ℂ) = (p : ℂ) * ((p : ℂ) - 1) / 2 := by
  have hd : 2 ∣ p * (p - 1) := by
    by_cases he : 2 ∣ p
    · exact dvd_mul_of_dvd_left he _
    · exact dvd_mul_of_dvd_right (by omega : 2 ∣ p - 1) _
  rw [Nat.cast_div_charZero hd, Nat.cast_mul, Nat.cast_sub hp] <;> norm_num

lemma period_coefficient_of_powers {p g : ℕ} (hp : 2 ≤ p)
    (hunit : ∀ j ∈ range (p - 1), ¬ p ∣ (g ^ p) ^ j)
    (hopposite : ∀ j ∈ range (p - 1), ∃ t ∈ range (p - 1),
      p ^ 2 ∣ (g ^ p) ^ j + (g ^ p) ^ t ∧
      ∀ l ∈ range (p - 1), l ≠ t → ¬ p ∣ (g ^ p) ^ j + (g ^ p) ^ l) :
    -(periodPolynomial p g).coeff (p - 2) = ((p * (p - 1) / 2 : ℕ) : ℂ) := by
  have hp' : 0 < p := by omega
  have hζ := period_root_is_primitive hp'
  have hsum : (∑ k ∈ range p, period p g k) = 0 :=
    OMA.PeriodMoments.firstMoment hp' (g ^ p) hζ hunit
  have hsq : (∑ k ∈ range p, (period p g k) ^ 2) = ((p - 1 : ℕ) : ℂ) * p :=
    OMA.PeriodMoments.secondMoment hp' (g ^ p) hζ hopposite
  have key := twice_shifted_coefficient (range p) (period p g)
  simp only [card_range, Polynomial.coeff_mul_X_pow', if_pos hp, hsum, hsq,
    Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at key
  rw [triangular_cast (by omega : 1 ≤ p)]
  unfold periodPolynomial
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  linear_combination -key

end OMA.CyclotomicPeriods

namespace Periods.CubeSum

open Finset BigOperators

private theorem residue_pair {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hab : a < p) (hsum : a + b = p) :
    a ^ 3 % p + b ^ 3 % p = p := by
  have hd : p ∣ a ^ 3 + b ^ 3 := by
    rw [← hsum]
    exact Odd.nat_add_dvd_pow_add_pow a b (show Odd 3 from ⟨1, rfl⟩)
  have hzero : (a ^ 3 % p + b ^ 3 % p) % p = 0 := by
    rw [← Nat.add_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  have hpos : a ^ 3 % p ≠ 0 := by
    intro hz
    have := Nat.le_of_dvd ha (hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero hz))
    omega
  have h₁ := Nat.mod_lt (a ^ 3) hp.pos
  have h₂ := Nat.mod_lt (b ^ 3) hp.pos
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hzero
  rcases q with _ | q
  · rw [Nat.mul_zero] at hq
    omega
  rcases q with _ | q
  · simpa using hq
  · have hlarge : p * 2 ≤ p * (q + 2) := Nat.mul_le_mul_left _ (by omega)
    change a ^ 3 % p + b ^ 3 % p = p * (q + 2) at hq
    omega

theorem twice_prime_cube_residue_sum (p : ℕ) (hp : p.Prime) :
    2 * (∑ k ∈ range p, k ^ 3 % p) = p * (p - 1) := by
  let f : ℕ → ℕ := fun k => k ^ 3 % p
  let N := p - 1
  have hN : N + 1 = p := by dsimp [N]; have := hp.pos; omega
  have hwhole : (∑ k ∈ range p, f k) = ∑ i ∈ range N, f (i + 1) := by
    calc
      _ = ∑ k ∈ range (N + 1), f k := by rw [hN]
      _ = _ := by rw [sum_range_succ']; simp [f]
  have reflect := sum_range_reflect (fun i => f (i + 1)) N
  have twice : (∑ i ∈ range N, f (i + 1)) + (∑ i ∈ range N, f (i + 1)) = N * p := by
    calc
      _ = (∑ i ∈ range N, f (i + 1)) + (∑ i ∈ range N, f (N - 1 - i + 1)) := by
        rw [reflect]
      _ = ∑ i ∈ range N, (f (i + 1) + f (N - 1 - i + 1)) := by rw [sum_add_distrib]
      _ = ∑ _i ∈ range N, p := by
        apply sum_congr rfl
        intro i hi
        have bound := mem_range.mp hi
        exact residue_pair (a := i + 1) (b := N - 1 - i + 1) hp
          (by omega) (by omega) (by omega)
      _ = N * p := by simp
  change 2 * (∑ k ∈ range p, f k) = _
  rw [hwhole, two_mul]
  exact twice.trans (Nat.mul_comm N p)

theorem prime_cube_residue_sum (p : ℕ) (hp : p.Prime) :
    (∑ k ∈ range p, k ^ 3 % p) = p * (p - 1) / 2 := by
  have h := twice_prime_cube_residue_sum p hp
  omega

end Periods.CubeSum

theorem OMA.solution : type_of% @OMA.S_oeis_a006308.main := by
  intro p g hp hp2 hg
  exact ⟨OMA.CyclotomicPeriods.period_coefficient_of_powers (by omega)
    (OMA.PeriodGroup.exponentUnits p g hp hp2 hg)
    (OMA.PeriodGroup.oppositeExponents p g hp hp2 hg),
    (Periods.CubeSum.prime_cube_residue_sum p hp).symm⟩

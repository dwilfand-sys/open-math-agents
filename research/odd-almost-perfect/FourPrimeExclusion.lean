import Mathlib

namespace OMA.OddAlmost

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

def factorBound (p : ℕ) : ℚ := 1 + 1 / ((p : ℚ) - 1)

lemma factorBound_antitone {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    factorBound q ≤ factorBound p := by
  have ht : (1 : ℚ) < p := by exact_mod_cast (by omega : 1 < p)
  have hle : (p : ℚ) ≤ q := by exact_mod_cast hpq
  unfold factorBound
  exact add_le_add_left (one_div_le_one_div_of_le (by linarith) (by linarith)) 1

lemma geometric_bound (p e : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ range (e + 1), (p : ℚ) ^ i) ≤ (p : ℚ) ^ e * factorBound p := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast (by omega : 1 < p)
  have hgeom := geom_sum_mul (p : ℚ) (e + 1)
  have hr : factorBound p = (p : ℚ) / ((p : ℚ) - 1) := by
    unfold factorBound
    field_simp [sub_ne_zero.mpr (ne_of_gt hp')] <;> ring
  rw [hr, ← mul_div_assoc, le_div_iff₀ (by linarith)]
  rw [hgeom, pow_succ]
  linarith

/-- The divisor ratio contributed by a single prime power. -/
private def localRatio (p e : ℕ) : ℚ :=
  (∑ j ∈ range (e + 1), (p : ℚ) ^ j) / (p : ℚ) ^ e

private theorem localRatio_nonneg (p e : ℕ) : 0 ≤ localRatio p e := by
  unfold localRatio
  exact div_nonneg (sum_nonneg fun _ _ => by positivity) (by positivity)

private theorem localRatio_mono {p k e : ℕ} (hp : 0 < p) (h : k ≤ e) :
    localRatio p k ≤ localRatio p e := by
  have hq : (0 : ℚ) < p := by exact_mod_cast hp
  induction e, h using Nat.le_induction with
  | base => rfl
  | succ e _ ih =>
    apply ih.trans
    have shift : (∑ j ∈ range (e + 1 + 1), (p : ℚ) ^ j) =
        (∑ j ∈ range (e + 1), (p : ℚ) ^ j) * p + 1 := by
      rw [sum_range_succ' (fun j => (p : ℚ) ^ j) (e + 1)]
      simp_rw [pow_succ]
      rw [← sum_mul, pow_zero]
    unfold localRatio
    rw [shift, pow_succ]
    apply (div_le_div_iff₀ (pow_pos hq _) (mul_pos (pow_pos hq _) hq)).mpr
    nlinarith only [pow_nonneg hq.le e]

private theorem localRatio_upper {p e : ℕ} (hp : 2 ≤ p) :
    localRatio p e ≤ factorBound p := by
  have hq : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  apply (div_le_iff₀ (pow_pos hq e)).mpr
  simpa [mul_comm] using geometric_bound p e hp

private theorem sigma_ratio_eq_prod {n : ℕ} (hn : 0 < n) :
    (σ 1 n : ℚ) / n = ∏ p ∈ n.primeFactors, localRatio p (n.factorization p) := by
  have hfactor : (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) = n := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  have hsum : (σ 1 n : ℚ) =
      ∏ p ∈ n.primeFactors, ∑ j ∈ range (n.factorization p + 1), (p : ℚ) ^ j := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne']
    push_cast <;> simp
  simp only [localRatio, prod_div_distrib, hfactor, ← hsum]

end OMA.OddAlmost

/-!
The checker associates an interval of possible divisor ratios with each
prime-power coordinate. Numeric leaves use only exact rational comparisons.
-/
namespace OMA.OddAlmost

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private structure FactorBox where
  prime : ℕ
  power : ℕ
  fixedPrime : Bool
  fixedPower : Bool

private def covers (b : FactorBox) (p e : ℕ) : Prop :=
  2 ≤ b.prime ∧ b.prime ≤ p ∧ b.power ≤ e ∧
  (b.fixedPrime = true → p = b.prime) ∧ (b.fixedPower = true → e = b.power)

private def boxLower (b : FactorBox) : ℚ :=
  if b.fixedPrime then localRatio b.prime b.power else 1

private def boxUpper (b : FactorBox) : ℚ :=
  if b.fixedPrime && b.fixedPower then localRatio b.prime b.power else factorBound b.prime

private lemma coordinate_bounds {b : FactorBox} {p e : ℕ} (hb : covers b p e) :
    boxLower b ≤ localRatio p e ∧ localRatio p e ≤ boxUpper b ∧ b.prime ^ b.power ≤ p ^ e := by
  obtain ⟨hb2, hbp, hbe, hp, he⟩ := hb
  have hp2 : 2 ≤ p := by omega
  have hpow : b.prime ^ b.power ≤ p ^ e := by
    calc
      b.prime ^ b.power ≤ p ^ b.power := Nat.pow_le_pow_left hbp _
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) hbe
  refine ⟨?_, ?_, hpow⟩
  · unfold boxLower
    by_cases h : b.fixedPrime = true
    · rw [if_pos h, hp h]
      exact localRatio_mono (by omega) hbe
    · rw [if_neg h]
      simpa [localRatio] using (localRatio_mono (p := p) (by omega) (Nat.zero_le e))
  · unfold boxUpper
    by_cases h : (b.fixedPrime && b.fixedPower) = true
    · have hpe := Bool.and_eq_true_iff.mp h
      rw [if_pos h, hp hpe.1, he hpe.2]
    · rw [if_neg h]
      exact (localRatio_upper hp2).trans (factorBound_antitone hb2 hbp)

private def excluded (box : Fin 4 → FactorBox) : Prop :=
  (∏ i, boxUpper (box i)) + 1 / (∏ i, ((box i).prime : ℚ) ^ (box i).power) < 2 ∨
  2 ≤ ∏ i, boxLower (box i)

private lemma excluded_false (box : Fin 4 → FactorBox) (p e : Fin 4 → ℕ)
    (heq : (∏ i, localRatio (p i) (e i)) + 1 / (∏ i, (p i : ℚ) ^ e i) = 2)
    (hc : ∀ i, covers (box i) (p i) (e i)) (hx : excluded box) : False := by
  have hm := fun i => coordinate_bounds (hc i)
  have hilo : ∀ i, 0 ≤ boxLower (box i) := by
    intro i
    unfold boxLower
    split
    · exact localRatio_nonneg _ _
    · norm_num
  have hip : ∀ i, 0 < (p i : ℚ) := by
    intro i
    exact_mod_cast (by have := (hc i).1; have := (hc i).2.1; omega : 0 < p i)
  have hbp : ∀ i, 0 < ((box i).prime : ℚ) := by
    intro i
    exact_mod_cast (by have := (hc i).1; omega : 0 < (box i).prime)
  have hN : 0 < ∏ i, (p i : ℚ) ^ e i :=
    prod_pos fun i _ => pow_pos (hip i) _
  have hB : 0 < ∏ i, ((box i).prime : ℚ) ^ (box i).power :=
    prod_pos fun i _ => pow_pos (hbp i) _
  have hBN : (∏ i, ((box i).prime : ℚ) ^ (box i).power) ≤ ∏ i, (p i : ℚ) ^ e i := by
    apply prod_le_prod
    · intro i _; exact (pow_pos (hbp i) _).le
    · intro i _; exact_mod_cast (hm i).2.2
  rcases hx with h | h
  · have hU : (∏ i, localRatio (p i) (e i)) ≤ ∏ i, boxUpper (box i) :=
      prod_le_prod (fun i _ => localRatio_nonneg _ _) (fun i _ => (hm i).2.1)
    linarith [one_div_le_one_div_of_le hB hBN]
  · have hL : (∏ i, boxLower (box i)) ≤ ∏ i, localRatio (p i) (e i) :=
      prod_le_prod (fun i _ => hilo i) (fun i _ => (hm i).1)
    linarith [one_div_pos.mpr hN]

private lemma skip_composites {a b p : ℕ} (hp : p.Prime) (hlt : a < p)
    (cert : ∀ j : Fin (b - a - 1), ¬ (a + 1 + j.val).Prime) : b ≤ p := by
  by_contra! hz
  have := cert ⟨p-a-1, by omega⟩
  exact this (by simpa [show a + 1 + (p - a - 1) = p by omega] using hp)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 90000000 in
private theorem four_intervals (p e : Fin 4 → ℕ) (hp : ∀ i, (p i).Prime)
    (ho : ∀ i, Odd (p i)) (hor : StrictMono p)
    (heven : ∀ i, Even (e i)) (hpos : ∀ i, 0 < e i)
    (heq : (∏ i, localRatio (p i) (e i)) + 1 / (∏ i, (p i : ℚ) ^ e i) = 2) : False := by
  have bad (box : Fin 4 → FactorBox) (hex : excluded box) (hc : ∀ i, covers (box i) (p i) (e i)) :
      False := excluded_false box p e heq hc hex
  obtain ⟨t0, hEven0⟩ := heven 0
  have hePos0 := hpos 0
  obtain ⟨t1, hEven1⟩ := heven 1
  have hePos1 := hpos 1
  have hIncreasing1 := hor (by decide : (0 : Fin 4) < 1)
  obtain ⟨t2, hEven2⟩ := heven 2
  have hePos2 := hpos 2
  have hIncreasing2 := hor (by decide : (1 : Fin 4) < 2)
  obtain ⟨t3, hEven3⟩ := heven 3
  have hePos3 := hpos 3
  have hIncreasing3 := hor (by decide : (2 : Fin 4) < 3)
  have hFirst : 3 ≤ p 0 := by
    obtain ⟨u, hu⟩ := ho 0
    have := (hp 0).two_le
    omega
  have p1ge5 : 5 ≤ p 1 := skip_composites (a := 3) (hp 1) (by omega) (by decide)
  have p2ge7 : 7 ≤ p 2 := skip_composites (a := 5) (hp 2) (by omega) (by decide)
  have p3ge11 : 11 ≤ p 3 := skip_composites (a := 7) (hp 3) (by omega) (by decide)
  by_cases h : p 0 = 3
  · by_cases h : p 1 = 5
    · by_cases h : p 2 = 7
      · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨7, 2, true, false⟩, ⟨11, 2, false, false⟩]
        · unfold excluded; decide +kernel
        · intro i; fin_cases i <;> simp [covers] <;> omega
      · have p2ge11 : 11 ≤ p 2 := skip_composites (a := 7) (hp 2) (by omega) (by decide)
        have p3ge13 : 13 ≤ p 3 := skip_composites (a := 11) (hp 3) (by omega) (by decide)
        by_cases h : p 2 = 11
        · by_cases h : p 3 = 13
          · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨13, 2, true, false⟩]
            · unfold excluded; decide +kernel
            · intro i; fin_cases i <;> simp [covers] <;> omega
          · have p3ge17 : 17 ≤ p 3 := skip_composites (a := 13) (hp 3) (by omega) (by decide)
            by_cases h : p 3 = 17
            · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨17, 2, true, false⟩]
              · unfold excluded; decide +kernel
              · intro i; fin_cases i <;> simp [covers] <;> omega
            · have p3ge19 : 19 ≤ p 3 := skip_composites (a := 17) (hp 3) (by omega) (by decide)
              by_cases h : p 3 = 19
              · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨19, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
              · have p3ge23 : 23 ≤ p 3 := skip_composites (a := 19) (hp 3) (by omega) (by decide)
                by_cases h : p 3 = 23
                · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨23, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
                · have p3ge29 : 29 ≤ p 3 := skip_composites (a := 23) (hp 3) (by omega) (by decide)
                  by_cases h : e 0 = 2
                  · by_cases h : p 3 = 29
                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨29, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · have p3ge31 : 31 ≤ p 3 := skip_composites (a := 29) (hp 3) (by omega) (by decide)
                      by_cases h : p 3 = 31
                      · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨31, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                        by_cases h : p 3 = 37
                        · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨37, 2, true, false⟩]
                          · unfold excluded; decide +kernel
                          · intro i; fin_cases i <;> simp [covers] <;> omega
                        · have p3ge41 : 41 ≤ p 3 := skip_composites (a := 37) (hp 3) (by omega) (by decide)
                          by_cases h : p 3 = 41
                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨41, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · have p3ge43 : 43 ≤ p 3 := skip_composites (a := 41) (hp 3) (by omega) (by decide)
                            by_cases h : p 3 = 43
                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨43, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                            · have p3ge47 : 47 ≤ p 3 := skip_composites (a := 43) (hp 3) (by omega) (by decide)
                              by_cases h : p 3 = 47
                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                · unfold excluded; decide +kernel
                                · intro i; fin_cases i <;> simp [covers] <;> omega
                              · have p3ge53 : 53 ≤ p 3 := skip_composites (a := 47) (hp 3) (by omega) (by decide)
                                by_cases h : p 3 = 53
                                · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨53, 2, true, false⟩]
                                  · unfold excluded; decide +kernel
                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                · have p3ge59 : 59 ≤ p 3 := skip_composites (a := 53) (hp 3) (by omega) (by decide)
                                  by_cases h : p 3 = 59
                                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨59, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                  · have p3ge61 : 61 ≤ p 3 := skip_composites (a := 59) (hp 3) (by omega) (by decide)
                                    by_cases h : p 3 = 61
                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨61, 2, true, false⟩]
                                      · unfold excluded; decide +kernel
                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                    · have p3ge67 : 67 ≤ p 3 := skip_composites (a := 61) (hp 3) (by omega) (by decide)
                                      by_cases h : p 3 = 67
                                      · by_cases h : e 1 = 2
                                        · by_cases h : e 2 = 2
                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, true⟩, ⟨67, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 4, true, false⟩, ⟨67, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                          · unfold excluded; decide +kernel
                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                      · have p3ge71 : 71 ≤ p 3 := skip_composites (a := 67) (hp 3) (by omega) (by decide)
                                        by_cases h : p 3 = 71
                                        · by_cases h : e 1 = 2
                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · have p3ge73 : 73 ≤ p 3 := skip_composites (a := 71) (hp 3) (by omega) (by decide)
                                          by_cases h : p 3 = 73
                                          · by_cases h : e 1 = 2
                                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · have p3ge79 : 79 ≤ p 3 := skip_composites (a := 73) (hp 3) (by omega) (by decide)
                                            by_cases h : p 3 = 79
                                            · by_cases h : e 1 = 2
                                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · have p3ge83 : 83 ≤ p 3 := skip_composites (a := 79) (hp 3) (by omega) (by decide)
                                              by_cases h : p 3 = 83
                                              · by_cases h : e 1 = 2
                                                · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · have p3ge89 : 89 ≤ p 3 := skip_composites (a := 83) (hp 3) (by omega) (by decide)
                                                by_cases h : p 3 = 89
                                                · by_cases h : e 1 = 2
                                                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · have p3ge97 : 97 ≤ p 3 := skip_composites (a := 89) (hp 3) (by omega) (by decide)
                                                  by_cases h : p 3 = 97
                                                  · by_cases h : e 1 = 2
                                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨97, 2, true, false⟩]
                                                      · unfold excluded; decide +kernel
                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨97, 2, true, false⟩]
                                                      · unfold excluded; decide +kernel
                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · have p3ge101 : 101 ≤ p 3 := skip_composites (a := 97) (hp 3) (by omega) (by decide)
                                                    by_cases h : p 3 = 101
                                                    · by_cases h : e 1 = 2
                                                      · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨101, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                      · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨101, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                    · have p3ge103 : 103 ≤ p 3 := skip_composites (a := 101) (hp 3) (by omega) (by decide)
                                                      by_cases h : p 3 = 103
                                                      · by_cases h : e 1 = 2
                                                        · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨103, 2, true, false⟩]
                                                          · unfold excluded; decide +kernel
                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                        · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨103, 2, true, false⟩]
                                                          · unfold excluded; decide +kernel
                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                      · have p3ge107 : 107 ≤ p 3 := skip_composites (a := 103) (hp 3) (by omega) (by decide)
                                                        by_cases h : p 3 = 107
                                                        · by_cases h : e 1 = 2
                                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨107, 2, true, false⟩]
                                                            · unfold excluded; decide +kernel
                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨107, 2, true, false⟩]
                                                            · unfold excluded; decide +kernel
                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                        · have p3ge109 : 109 ≤ p 3 := skip_composites (a := 107) (hp 3) (by omega) (by decide)
                                                          by_cases h : p 3 = 109
                                                          · by_cases h : e 1 = 2
                                                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨109, 2, true, false⟩]
                                                              · unfold excluded; decide +kernel
                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨109, 2, true, false⟩]
                                                              · unfold excluded; decide +kernel
                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                          · have p3ge113 : 113 ≤ p 3 := skip_composites (a := 109) (hp 3) (by omega) (by decide)
                                                            by_cases h : p 3 = 113
                                                            · by_cases h : e 1 = 2
                                                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨113, 2, true, false⟩]
                                                                · unfold excluded; decide +kernel
                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨113, 2, true, false⟩]
                                                                · unfold excluded; decide +kernel
                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                            · have p3ge127 : 127 ≤ p 3 := skip_composites (a := 113) (hp 3) (by omega) (by decide)
                                                              by_cases h : e 1 = 2
                                                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨127, 2, false, false⟩]
                                                                · unfold excluded; decide +kernel
                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                              · by_cases h : p 3 = 127
                                                                · by_cases h : e 2 = 2
                                                                  · by_cases h : e 1 = 4
                                                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, true⟩, ⟨11, 2, true, true⟩, ⟨127, 2, true, false⟩]
                                                                      · unfold excluded; decide +kernel
                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 6, true, false⟩, ⟨11, 2, true, true⟩, ⟨127, 2, true, false⟩]
                                                                      · unfold excluded; decide +kernel
                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 4, true, false⟩, ⟨127, 2, true, false⟩]
                                                                    · unfold excluded; decide +kernel
                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                · have p3ge131 : 131 ≤ p 3 := skip_composites (a := 127) (hp 3) (by omega) (by decide)
                                                                  by_cases h : p 3 = 131
                                                                  · by_cases h : e 2 = 2
                                                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, true⟩, ⟨131, 2, true, false⟩]
                                                                      · unfold excluded; decide +kernel
                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 4, true, false⟩, ⟨131, 2, true, false⟩]
                                                                      · unfold excluded; decide +kernel
                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                  · have p3ge137 : 137 ≤ p 3 := skip_composites (a := 131) (hp 3) (by omega) (by decide)
                                                                    by_cases h : p 3 = 137
                                                                    · by_cases h : e 2 = 2
                                                                      · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, true⟩, ⟨137, 2, true, false⟩]
                                                                        · unfold excluded; decide +kernel
                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                      · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 4, true, false⟩, ⟨137, 2, true, false⟩]
                                                                        · unfold excluded; decide +kernel
                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                    · have p3ge139 : 139 ≤ p 3 := skip_composites (a := 137) (hp 3) (by omega) (by decide)
                                                                      by_cases h : p 3 = 139
                                                                      · by_cases h : e 2 = 2
                                                                        · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, true⟩, ⟨139, 2, true, false⟩]
                                                                          · unfold excluded; decide +kernel
                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                        · by_cases h : e 1 = 4
                                                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, true⟩, ⟨11, 4, true, false⟩, ⟨139, 2, true, false⟩]
                                                                            · unfold excluded; decide +kernel
                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 6, true, false⟩, ⟨11, 4, true, false⟩, ⟨139, 2, true, false⟩]
                                                                            · unfold excluded; decide +kernel
                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                      · have p3ge149 : 149 ≤ p 3 := skip_composites (a := 139) (hp 3) (by omega) (by decide)
                                                                        apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨149, 2, false, false⟩]
                                                                        · unfold excluded; decide +kernel
                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨29, 2, false, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
        · have p2ge13 : 13 ≤ p 2 := skip_composites (a := 11) (hp 2) (by omega) (by decide)
          have p3ge17 : 17 ≤ p 3 := skip_composites (a := 13) (hp 3) (by omega) (by decide)
          by_cases h : p 2 = 13
          · by_cases h : p 3 = 17
            · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨17, 2, true, false⟩]
              · unfold excluded; decide +kernel
              · intro i; fin_cases i <;> simp [covers] <;> omega
            · have p3ge19 : 19 ≤ p 3 := skip_composites (a := 17) (hp 3) (by omega) (by decide)
              by_cases h : p 3 = 19
              · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨19, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
              · have p3ge23 : 23 ≤ p 3 := skip_composites (a := 19) (hp 3) (by omega) (by decide)
                by_cases h : p 3 = 23
                · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨23, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
                · have p3ge29 : 29 ≤ p 3 := skip_composites (a := 23) (hp 3) (by omega) (by decide)
                  by_cases h : e 0 = 2
                  · by_cases h : p 3 = 29
                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨29, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · have p3ge31 : 31 ≤ p 3 := skip_composites (a := 29) (hp 3) (by omega) (by decide)
                      by_cases h : p 3 = 31
                      · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨31, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                        by_cases h : p 3 = 37
                        · by_cases h : e 1 = 2
                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨13, 2, true, false⟩, ⟨37, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨13, 2, true, false⟩, ⟨37, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                        · have p3ge41 : 41 ≤ p 3 := skip_composites (a := 37) (hp 3) (by omega) (by decide)
                          by_cases h : p 3 = 41
                          · by_cases h : e 1 = 2
                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨13, 2, true, false⟩, ⟨41, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                            · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨13, 2, true, false⟩, ⟨41, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                          · have p3ge43 : 43 ≤ p 3 := skip_composites (a := 41) (hp 3) (by omega) (by decide)
                            by_cases h : p 3 = 43
                            · by_cases h : e 1 = 2
                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨13, 2, true, false⟩, ⟨43, 2, true, false⟩]
                                · unfold excluded; decide +kernel
                                · intro i; fin_cases i <;> simp [covers] <;> omega
                              · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨13, 2, true, false⟩, ⟨43, 2, true, false⟩]
                                · unfold excluded; decide +kernel
                                · intro i; fin_cases i <;> simp [covers] <;> omega
                            · have p3ge47 : 47 ≤ p 3 := skip_composites (a := 43) (hp 3) (by omega) (by decide)
                              apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨47, 2, false, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨29, 2, false, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
          · have p2ge17 : 17 ≤ p 2 := skip_composites (a := 13) (hp 2) (by omega) (by decide)
            have p3ge19 : 19 ≤ p 3 := skip_composites (a := 17) (hp 3) (by omega) (by decide)
            by_cases h : p 2 = 17
            · by_cases h : p 3 = 19
              · apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨19, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
              · have p3ge23 : 23 ≤ p 3 := skip_composites (a := 19) (hp 3) (by omega) (by decide)
                by_cases h : p 3 = 23
                · by_cases h : e 0 = 2
                  · by_cases h : e 1 = 2
                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨23, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨23, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨23, 2, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                · have p3ge29 : 29 ≤ p 3 := skip_composites (a := 23) (hp 3) (by omega) (by decide)
                  by_cases h : e 0 = 2
                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨29, 2, false, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · by_cases h : p 3 = 29
                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨29, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · have p3ge31 : 31 ≤ p 3 := skip_composites (a := 29) (hp 3) (by omega) (by decide)
                      by_cases h : p 3 = 31
                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨31, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                        by_cases h : p 3 = 37
                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨37, 2, true, false⟩]
                          · unfold excluded; decide +kernel
                          · intro i; fin_cases i <;> simp [covers] <;> omega
                        · have p3ge41 : 41 ≤ p 3 := skip_composites (a := 37) (hp 3) (by omega) (by decide)
                          by_cases h : p 3 = 41
                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨41, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · have p3ge43 : 43 ≤ p 3 := skip_composites (a := 41) (hp 3) (by omega) (by decide)
                            by_cases h : p 3 = 43
                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨43, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                            · have p3ge47 : 47 ≤ p 3 := skip_composites (a := 43) (hp 3) (by omega) (by decide)
                              by_cases h : p 3 = 47
                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                · unfold excluded; decide +kernel
                                · intro i; fin_cases i <;> simp [covers] <;> omega
                              · have p3ge53 : 53 ≤ p 3 := skip_composites (a := 47) (hp 3) (by omega) (by decide)
                                by_cases h : p 3 = 53
                                · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨53, 2, true, false⟩]
                                  · unfold excluded; decide +kernel
                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                · have p3ge59 : 59 ≤ p 3 := skip_composites (a := 53) (hp 3) (by omega) (by decide)
                                  by_cases h : p 3 = 59
                                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨59, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                  · have p3ge61 : 61 ≤ p 3 := skip_composites (a := 59) (hp 3) (by omega) (by decide)
                                    by_cases h : p 3 = 61
                                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨17, 2, true, false⟩, ⟨61, 2, true, false⟩]
                                      · unfold excluded; decide +kernel
                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                    · have p3ge67 : 67 ≤ p 3 := skip_composites (a := 61) (hp 3) (by omega) (by decide)
                                      by_cases h : p 3 = 67
                                      · by_cases h : e 1 = 2
                                        · by_cases h : e 0 = 4
                                          · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · apply bad ![⟨3, 6, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                          · unfold excluded; decide +kernel
                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                      · have p3ge71 : 71 ≤ p 3 := skip_composites (a := 67) (hp 3) (by omega) (by decide)
                                        by_cases h : p 3 = 71
                                        · by_cases h : e 1 = 2
                                          · by_cases h : e 0 = 4
                                            · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · apply bad ![⟨3, 6, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · have p3ge73 : 73 ≤ p 3 := skip_composites (a := 71) (hp 3) (by omega) (by decide)
                                          by_cases h : p 3 = 73
                                          · by_cases h : e 1 = 2
                                            · by_cases h : e 0 = 4
                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · apply bad ![⟨3, 6, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · have p3ge79 : 79 ≤ p 3 := skip_composites (a := 73) (hp 3) (by omega) (by decide)
                                            by_cases h : p 3 = 79
                                            · by_cases h : e 1 = 2
                                              · by_cases h : e 0 = 4
                                                · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · apply bad ![⟨3, 6, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · have p3ge83 : 83 ≤ p 3 := skip_composites (a := 79) (hp 3) (by omega) (by decide)
                                              by_cases h : p 3 = 83
                                              · by_cases h : e 1 = 2
                                                · by_cases h : e 0 = 4
                                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · by_cases h : e 0 = 6
                                                    · apply bad ![⟨3, 6, true, true⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                      · unfold excluded; decide +kernel
                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                    · by_cases h : e 2 = 2
                                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, true⟩, ⟨83, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 4, true, false⟩, ⟨83, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · have p3ge89 : 89 ≤ p 3 := skip_composites (a := 83) (hp 3) (by omega) (by decide)
                                                by_cases h : p 3 = 89
                                                · by_cases h : e 1 = 2
                                                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · have p3ge97 : 97 ≤ p 3 := skip_composites (a := 89) (hp 3) (by omega) (by decide)
                                                  by_cases h : p 3 = 97
                                                  · by_cases h : e 1 = 2
                                                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨97, 2, true, false⟩]
                                                      · unfold excluded; decide +kernel
                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨97, 2, true, false⟩]
                                                      · unfold excluded; decide +kernel
                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · have p3ge101 : 101 ≤ p 3 := skip_composites (a := 97) (hp 3) (by omega) (by decide)
                                                    by_cases h : p 3 = 101
                                                    · by_cases h : e 1 = 2
                                                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨101, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨101, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                    · have p3ge103 : 103 ≤ p 3 := skip_composites (a := 101) (hp 3) (by omega) (by decide)
                                                      by_cases h : p 3 = 103
                                                      · by_cases h : e 1 = 2
                                                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨103, 2, true, false⟩]
                                                          · unfold excluded; decide +kernel
                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨103, 2, true, false⟩]
                                                          · unfold excluded; decide +kernel
                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                      · have p3ge107 : 107 ≤ p 3 := skip_composites (a := 103) (hp 3) (by omega) (by decide)
                                                        by_cases h : p 3 = 107
                                                        · by_cases h : e 1 = 2
                                                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨107, 2, true, false⟩]
                                                            · unfold excluded; decide +kernel
                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨107, 2, true, false⟩]
                                                            · unfold excluded; decide +kernel
                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                        · have p3ge109 : 109 ≤ p 3 := skip_composites (a := 107) (hp 3) (by omega) (by decide)
                                                          by_cases h : p 3 = 109
                                                          · by_cases h : e 1 = 2
                                                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨109, 2, true, false⟩]
                                                              · unfold excluded; decide +kernel
                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨109, 2, true, false⟩]
                                                              · unfold excluded; decide +kernel
                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                          · have p3ge113 : 113 ≤ p 3 := skip_composites (a := 109) (hp 3) (by omega) (by decide)
                                                            by_cases h : p 3 = 113
                                                            · by_cases h : e 1 = 2
                                                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨113, 2, true, false⟩]
                                                                · unfold excluded; decide +kernel
                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨113, 2, true, false⟩]
                                                                · unfold excluded; decide +kernel
                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                            · have p3ge127 : 127 ≤ p 3 := skip_composites (a := 113) (hp 3) (by omega) (by decide)
                                                              by_cases h : e 1 = 2
                                                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨17, 2, true, false⟩, ⟨127, 2, false, false⟩]
                                                                · unfold excluded; decide +kernel
                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                              · by_cases h : p 3 = 127
                                                                · by_cases h : e 0 = 4
                                                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨127, 2, true, false⟩]
                                                                    · unfold excluded; decide +kernel
                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                  · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨127, 2, true, false⟩]
                                                                    · unfold excluded; decide +kernel
                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                · have p3ge131 : 131 ≤ p 3 := skip_composites (a := 127) (hp 3) (by omega) (by decide)
                                                                  by_cases h : p 3 = 131
                                                                  · by_cases h : e 0 = 4
                                                                    · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨131, 2, true, false⟩]
                                                                      · unfold excluded; decide +kernel
                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                    · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨131, 2, true, false⟩]
                                                                      · unfold excluded; decide +kernel
                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                  · have p3ge137 : 137 ≤ p 3 := skip_composites (a := 131) (hp 3) (by omega) (by decide)
                                                                    by_cases h : p 3 = 137
                                                                    · by_cases h : e 0 = 4
                                                                      · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨137, 2, true, false⟩]
                                                                        · unfold excluded; decide +kernel
                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                      · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨137, 2, true, false⟩]
                                                                        · unfold excluded; decide +kernel
                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                    · have p3ge139 : 139 ≤ p 3 := skip_composites (a := 137) (hp 3) (by omega) (by decide)
                                                                      by_cases h : p 3 = 139
                                                                      · by_cases h : e 0 = 4
                                                                        · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨139, 2, true, false⟩]
                                                                          · unfold excluded; decide +kernel
                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                        · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨139, 2, true, false⟩]
                                                                          · unfold excluded; decide +kernel
                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                      · have p3ge149 : 149 ≤ p 3 := skip_composites (a := 139) (hp 3) (by omega) (by decide)
                                                                        by_cases h : p 3 = 149
                                                                        · by_cases h : e 0 = 4
                                                                          · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨149, 2, true, false⟩]
                                                                            · unfold excluded; decide +kernel
                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                          · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨149, 2, true, false⟩]
                                                                            · unfold excluded; decide +kernel
                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                        · have p3ge151 : 151 ≤ p 3 := skip_composites (a := 149) (hp 3) (by omega) (by decide)
                                                                          by_cases h : p 3 = 151
                                                                          · by_cases h : e 0 = 4
                                                                            · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨151, 2, true, false⟩]
                                                                              · unfold excluded; decide +kernel
                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                            · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨151, 2, true, false⟩]
                                                                              · unfold excluded; decide +kernel
                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                          · have p3ge157 : 157 ≤ p 3 := skip_composites (a := 151) (hp 3) (by omega) (by decide)
                                                                            by_cases h : p 3 = 157
                                                                            · by_cases h : e 0 = 4
                                                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨157, 2, true, false⟩]
                                                                                · unfold excluded; decide +kernel
                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                              · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨157, 2, true, false⟩]
                                                                                · unfold excluded; decide +kernel
                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                            · have p3ge163 : 163 ≤ p 3 := skip_composites (a := 157) (hp 3) (by omega) (by decide)
                                                                              by_cases h : p 3 = 163
                                                                              · by_cases h : e 0 = 4
                                                                                · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨163, 2, true, false⟩]
                                                                                  · unfold excluded; decide +kernel
                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨163, 2, true, false⟩]
                                                                                  · unfold excluded; decide +kernel
                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                              · have p3ge167 : 167 ≤ p 3 := skip_composites (a := 163) (hp 3) (by omega) (by decide)
                                                                                by_cases h : p 3 = 167
                                                                                · by_cases h : e 0 = 4
                                                                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨167, 2, true, false⟩]
                                                                                    · unfold excluded; decide +kernel
                                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                  · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨167, 2, true, false⟩]
                                                                                    · unfold excluded; decide +kernel
                                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                · have p3ge173 : 173 ≤ p 3 := skip_composites (a := 167) (hp 3) (by omega) (by decide)
                                                                                  by_cases h : p 3 = 173
                                                                                  · by_cases h : e 0 = 4
                                                                                    · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨173, 2, true, false⟩]
                                                                                      · unfold excluded; decide +kernel
                                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                    · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨173, 2, true, false⟩]
                                                                                      · unfold excluded; decide +kernel
                                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                  · have p3ge179 : 179 ≤ p 3 := skip_composites (a := 173) (hp 3) (by omega) (by decide)
                                                                                    by_cases h : p 3 = 179
                                                                                    · by_cases h : e 0 = 4
                                                                                      · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨179, 2, true, false⟩]
                                                                                        · unfold excluded; decide +kernel
                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                      · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨179, 2, true, false⟩]
                                                                                        · unfold excluded; decide +kernel
                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                    · have p3ge181 : 181 ≤ p 3 := skip_composites (a := 179) (hp 3) (by omega) (by decide)
                                                                                      by_cases h : p 3 = 181
                                                                                      · by_cases h : e 0 = 4
                                                                                        · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨181, 2, true, false⟩]
                                                                                          · unfold excluded; decide +kernel
                                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                        · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨181, 2, true, false⟩]
                                                                                          · unfold excluded; decide +kernel
                                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                      · have p3ge191 : 191 ≤ p 3 := skip_composites (a := 181) (hp 3) (by omega) (by decide)
                                                                                        by_cases h : p 3 = 191
                                                                                        · by_cases h : e 0 = 4
                                                                                          · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨191, 2, true, false⟩]
                                                                                            · unfold excluded; decide +kernel
                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                          · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨191, 2, true, false⟩]
                                                                                            · unfold excluded; decide +kernel
                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                        · have p3ge193 : 193 ≤ p 3 := skip_composites (a := 191) (hp 3) (by omega) (by decide)
                                                                                          by_cases h : p 3 = 193
                                                                                          · by_cases h : e 0 = 4
                                                                                            · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨193, 2, true, false⟩]
                                                                                              · unfold excluded; decide +kernel
                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                            · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨193, 2, true, false⟩]
                                                                                              · unfold excluded; decide +kernel
                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                          · have p3ge197 : 197 ≤ p 3 := skip_composites (a := 193) (hp 3) (by omega) (by decide)
                                                                                            by_cases h : p 3 = 197
                                                                                            · by_cases h : e 0 = 4
                                                                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨197, 2, true, false⟩]
                                                                                                · unfold excluded; decide +kernel
                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                              · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨197, 2, true, false⟩]
                                                                                                · unfold excluded; decide +kernel
                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                            · have p3ge199 : 199 ≤ p 3 := skip_composites (a := 197) (hp 3) (by omega) (by decide)
                                                                                              by_cases h : p 3 = 199
                                                                                              · by_cases h : e 0 = 4
                                                                                                · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨199, 2, true, false⟩]
                                                                                                  · unfold excluded; decide +kernel
                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨199, 2, true, false⟩]
                                                                                                  · unfold excluded; decide +kernel
                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                              · have p3ge211 : 211 ≤ p 3 := skip_composites (a := 199) (hp 3) (by omega) (by decide)
                                                                                                by_cases h : p 3 = 211
                                                                                                · by_cases h : e 0 = 4
                                                                                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨211, 2, true, false⟩]
                                                                                                    · unfold excluded; decide +kernel
                                                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                  · by_cases h : e 0 = 6
                                                                                                    · by_cases h : e 1 = 4
                                                                                                      · by_cases h : e 2 = 2
                                                                                                        · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, true⟩, ⟨211, 2, true, false⟩]
                                                                                                          · unfold excluded; decide +kernel
                                                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                        · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨17, 4, true, false⟩, ⟨211, 2, true, false⟩]
                                                                                                          · unfold excluded; decide +kernel
                                                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                      · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, false⟩, ⟨211, 2, true, false⟩]
                                                                                                        · unfold excluded; decide +kernel
                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                    · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨211, 2, true, false⟩]
                                                                                                      · unfold excluded; decide +kernel
                                                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                · have p3ge223 : 223 ≤ p 3 := skip_composites (a := 211) (hp 3) (by omega) (by decide)
                                                                                                  by_cases h : p 3 = 223
                                                                                                  · by_cases h : e 0 = 4
                                                                                                    · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨223, 2, true, false⟩]
                                                                                                      · unfold excluded; decide +kernel
                                                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                    · by_cases h : e 0 = 6
                                                                                                      · by_cases h : e 1 = 4
                                                                                                        · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, false⟩, ⟨223, 2, true, false⟩]
                                                                                                          · unfold excluded; decide +kernel
                                                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                        · by_cases h : e 2 = 2
                                                                                                          · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, true⟩, ⟨223, 2, true, false⟩]
                                                                                                            · unfold excluded; decide +kernel
                                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                          · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 4, true, false⟩, ⟨223, 2, true, false⟩]
                                                                                                            · unfold excluded; decide +kernel
                                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨223, 2, true, false⟩]
                                                                                                        · unfold excluded; decide +kernel
                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                  · have p3ge227 : 227 ≤ p 3 := skip_composites (a := 223) (hp 3) (by omega) (by decide)
                                                                                                    by_cases h : p 3 = 227
                                                                                                    · by_cases h : e 0 = 4
                                                                                                      · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨227, 2, true, false⟩]
                                                                                                        · unfold excluded; decide +kernel
                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                      · by_cases h : e 0 = 6
                                                                                                        · by_cases h : e 1 = 4
                                                                                                          · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, false⟩, ⟨227, 2, true, false⟩]
                                                                                                            · unfold excluded; decide +kernel
                                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                          · by_cases h : e 2 = 2
                                                                                                            · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, true⟩, ⟨227, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 4, true, false⟩, ⟨227, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                        · by_cases h : e 1 = 4
                                                                                                          · by_cases h : e 2 = 2
                                                                                                            · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, true⟩, ⟨227, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 4, true, false⟩, ⟨227, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                          · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, false⟩, ⟨227, 2, true, false⟩]
                                                                                                            · unfold excluded; decide +kernel
                                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                    · have p3ge229 : 229 ≤ p 3 := skip_composites (a := 227) (hp 3) (by omega) (by decide)
                                                                                                      by_cases h : p 3 = 229
                                                                                                      · by_cases h : e 0 = 4
                                                                                                        · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨229, 2, true, false⟩]
                                                                                                          · unfold excluded; decide +kernel
                                                                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                        · by_cases h : e 0 = 6
                                                                                                          · by_cases h : e 1 = 4
                                                                                                            · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, false⟩, ⟨229, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · by_cases h : e 2 = 2
                                                                                                              · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, true⟩, ⟨229, 2, true, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                              · by_cases h : e 1 = 6
                                                                                                                · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, true⟩, ⟨17, 4, true, false⟩, ⟨229, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                · apply bad ![⟨3, 6, true, true⟩, ⟨5, 8, true, false⟩, ⟨17, 4, true, false⟩, ⟨229, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                          · by_cases h : e 1 = 4
                                                                                                            · by_cases h : e 2 = 2
                                                                                                              · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, true⟩, ⟨229, 2, true, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                              · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 4, true, false⟩, ⟨229, 2, true, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, false⟩, ⟨229, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                      · have p3ge233 : 233 ≤ p 3 := skip_composites (a := 229) (hp 3) (by omega) (by decide)
                                                                                                        by_cases h : p 3 = 233
                                                                                                        · by_cases h : e 0 = 4
                                                                                                          · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨233, 2, true, false⟩]
                                                                                                            · unfold excluded; decide +kernel
                                                                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                          · by_cases h : e 0 = 6
                                                                                                            · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨233, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · by_cases h : e 1 = 4
                                                                                                              · by_cases h : e 2 = 2
                                                                                                                · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, true⟩, ⟨233, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 4, true, false⟩, ⟨233, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                              · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, false⟩, ⟨233, 2, true, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                        · have p3ge239 : 239 ≤ p 3 := skip_composites (a := 233) (hp 3) (by omega) (by decide)
                                                                                                          by_cases h : p 3 = 239
                                                                                                          · by_cases h : e 0 = 4
                                                                                                            · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨239, 2, true, false⟩]
                                                                                                              · unfold excluded; decide +kernel
                                                                                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · by_cases h : e 0 = 6
                                                                                                              · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨239, 2, true, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                              · by_cases h : e 1 = 4
                                                                                                                · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, false⟩, ⟨239, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, false⟩, ⟨239, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                          · have p3ge241 : 241 ≤ p 3 := skip_composites (a := 239) (hp 3) (by omega) (by decide)
                                                                                                            by_cases h : p 3 = 241
                                                                                                            · by_cases h : e 0 = 4
                                                                                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨241, 2, true, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                              · by_cases h : e 0 = 6
                                                                                                                · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨241, 2, true, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                · by_cases h : e 1 = 4
                                                                                                                  · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, false⟩, ⟨241, 2, true, false⟩]
                                                                                                                    · unfold excluded; decide +kernel
                                                                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                  · by_cases h : e 2 = 2
                                                                                                                    · by_cases h : e 0 = 8
                                                                                                                      · apply bad ![⟨3, 8, true, true⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, true⟩, ⟨241, 2, true, false⟩]
                                                                                                                        · unfold excluded; decide +kernel
                                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                      · apply bad ![⟨3, 10, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, true⟩, ⟨241, 2, true, false⟩]
                                                                                                                        · unfold excluded; decide +kernel
                                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                    · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 4, true, false⟩, ⟨241, 2, true, false⟩]
                                                                                                                      · unfold excluded; decide +kernel
                                                                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                            · have p3ge251 : 251 ≤ p 3 := skip_composites (a := 241) (hp 3) (by omega) (by decide)
                                                                                                              by_cases h : e 0 = 4
                                                                                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨251, 2, false, false⟩]
                                                                                                                · unfold excluded; decide +kernel
                                                                                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                              · by_cases h : p 3 = 251
                                                                                                                · by_cases h : e 0 = 6
                                                                                                                  · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨251, 2, true, false⟩]
                                                                                                                    · unfold excluded; decide +kernel
                                                                                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                  · by_cases h : e 1 = 4
                                                                                                                    · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, true⟩, ⟨17, 2, true, false⟩, ⟨251, 2, true, false⟩]
                                                                                                                      · unfold excluded; decide +kernel
                                                                                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                    · by_cases h : e 2 = 2
                                                                                                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 2, true, true⟩, ⟨251, 2, true, false⟩]
                                                                                                                        · unfold excluded; decide +kernel
                                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 6, true, false⟩, ⟨17, 4, true, false⟩, ⟨251, 2, true, false⟩]
                                                                                                                        · unfold excluded; decide +kernel
                                                                                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                                                                                · have p3ge257 : 257 ≤ p 3 := skip_composites (a := 251) (hp 3) (by omega) (by decide)
                                                                                                                  apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨17, 2, true, false⟩, ⟨257, 2, false, false⟩]
                                                                                                                  · unfold excluded; decide +kernel
                                                                                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
            · have p2ge19 : 19 ≤ p 2 := skip_composites (a := 17) (hp 2) (by omega) (by decide)
              have p3ge23 : 23 ≤ p 3 := skip_composites (a := 19) (hp 3) (by omega) (by decide)
              by_cases h : p 2 = 19
              · by_cases h : p 3 = 23
                · by_cases h : e 0 = 2
                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨23, 2, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨23, 2, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                · have p3ge29 : 29 ≤ p 3 := skip_composites (a := 23) (hp 3) (by omega) (by decide)
                  by_cases h : e 0 = 2
                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨29, 2, false, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · by_cases h : p 3 = 29
                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨29, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · have p3ge31 : 31 ≤ p 3 := skip_composites (a := 29) (hp 3) (by omega) (by decide)
                      by_cases h : p 3 = 31
                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨31, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                        by_cases h : p 3 = 37
                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨37, 2, true, false⟩]
                          · unfold excluded; decide +kernel
                          · intro i; fin_cases i <;> simp [covers] <;> omega
                        · have p3ge41 : 41 ≤ p 3 := skip_composites (a := 37) (hp 3) (by omega) (by decide)
                          by_cases h : p 3 = 41
                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨41, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · have p3ge43 : 43 ≤ p 3 := skip_composites (a := 41) (hp 3) (by omega) (by decide)
                            by_cases h : p 3 = 43
                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨43, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                            · have p3ge47 : 47 ≤ p 3 := skip_composites (a := 43) (hp 3) (by omega) (by decide)
                              by_cases h : p 3 = 47
                              · by_cases h : e 1 = 2
                                · by_cases h : e 0 = 4
                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                  · apply bad ![⟨3, 6, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                  · unfold excluded; decide +kernel
                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                              · have p3ge53 : 53 ≤ p 3 := skip_composites (a := 47) (hp 3) (by omega) (by decide)
                                by_cases h : p 3 = 53
                                · by_cases h : e 1 = 2
                                  · by_cases h : e 0 = 4
                                    · apply bad ![⟨3, 4, true, true⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨53, 2, true, false⟩]
                                      · unfold excluded; decide +kernel
                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                    · by_cases h : e 0 = 6
                                      · by_cases h : e 2 = 2
                                        · apply bad ![⟨3, 6, true, true⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, true⟩, ⟨53, 2, true, false⟩]
                                          · unfold excluded; decide +kernel
                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · apply bad ![⟨3, 6, true, true⟩, ⟨5, 2, true, true⟩, ⟨19, 4, true, false⟩, ⟨53, 2, true, false⟩]
                                          · unfold excluded; decide +kernel
                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨53, 2, true, false⟩]
                                        · unfold excluded; decide +kernel
                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨53, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                · have p3ge59 : 59 ≤ p 3 := skip_composites (a := 53) (hp 3) (by omega) (by decide)
                                  by_cases h : p 3 = 59
                                  · by_cases h : e 1 = 2
                                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨59, 2, true, false⟩]
                                      · unfold excluded; decide +kernel
                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨59, 2, true, false⟩]
                                      · unfold excluded; decide +kernel
                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                  · have p3ge61 : 61 ≤ p 3 := skip_composites (a := 59) (hp 3) (by omega) (by decide)
                                    by_cases h : p 3 = 61
                                    · by_cases h : e 1 = 2
                                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨61, 2, true, false⟩]
                                        · unfold excluded; decide +kernel
                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨61, 2, true, false⟩]
                                        · unfold excluded; decide +kernel
                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                    · have p3ge67 : 67 ≤ p 3 := skip_composites (a := 61) (hp 3) (by omega) (by decide)
                                      by_cases h : p 3 = 67
                                      · by_cases h : e 1 = 2
                                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                          · unfold excluded; decide +kernel
                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · by_cases h : e 0 = 4
                                          · by_cases h : e 1 = 4
                                            · by_cases h : e 2 = 2
                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, true⟩, ⟨19, 2, true, true⟩, ⟨67, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, true⟩, ⟨19, 4, true, false⟩, ⟨67, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · apply bad ![⟨3, 4, true, true⟩, ⟨5, 6, true, false⟩, ⟨19, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨67, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                      · have p3ge71 : 71 ≤ p 3 := skip_composites (a := 67) (hp 3) (by omega) (by decide)
                                        by_cases h : p 3 = 71
                                        · by_cases h : e 1 = 2
                                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                            · unfold excluded; decide +kernel
                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · by_cases h : e 0 = 4
                                            · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨71, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                        · have p3ge73 : 73 ≤ p 3 := skip_composites (a := 71) (hp 3) (by omega) (by decide)
                                          by_cases h : p 3 = 73
                                          · by_cases h : e 1 = 2
                                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                              · unfold excluded; decide +kernel
                                              · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · by_cases h : e 0 = 4
                                              · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨73, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                          · have p3ge79 : 79 ≤ p 3 := skip_composites (a := 73) (hp 3) (by omega) (by decide)
                                            by_cases h : p 3 = 79
                                            · by_cases h : e 1 = 2
                                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                · unfold excluded; decide +kernel
                                                · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · by_cases h : e 0 = 4
                                                · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨79, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                            · have p3ge83 : 83 ≤ p 3 := skip_composites (a := 79) (hp 3) (by omega) (by decide)
                                              by_cases h : p 3 = 83
                                              · by_cases h : e 1 = 2
                                                · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · by_cases h : e 0 = 4
                                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨83, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                              · have p3ge89 : 89 ≤ p 3 := skip_composites (a := 83) (hp 3) (by omega) (by decide)
                                                by_cases h : p 3 = 89
                                                · by_cases h : e 1 = 2
                                                  · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨19, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                    · unfold excluded; decide +kernel
                                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                                  · by_cases h : e 0 = 4
                                                    · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                      · unfold excluded; decide +kernel
                                                      · intro i; fin_cases i <;> simp [covers] <;> omega
                                                    · by_cases h : e 0 = 6
                                                      · by_cases h : e 1 = 4
                                                        · by_cases h : e 2 = 2
                                                          · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨19, 2, true, true⟩, ⟨89, 2, true, false⟩]
                                                            · unfold excluded; decide +kernel
                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                          · apply bad ![⟨3, 6, true, true⟩, ⟨5, 4, true, true⟩, ⟨19, 4, true, false⟩, ⟨89, 2, true, false⟩]
                                                            · unfold excluded; decide +kernel
                                                            · intro i; fin_cases i <;> simp [covers] <;> omega
                                                        · apply bad ![⟨3, 6, true, true⟩, ⟨5, 6, true, false⟩, ⟨19, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                          · unfold excluded; decide +kernel
                                                          · intro i; fin_cases i <;> simp [covers] <;> omega
                                                      · apply bad ![⟨3, 8, true, false⟩, ⟨5, 4, true, false⟩, ⟨19, 2, true, false⟩, ⟨89, 2, true, false⟩]
                                                        · unfold excluded; decide +kernel
                                                        · intro i; fin_cases i <;> simp [covers] <;> omega
                                                · have p3ge97 : 97 ≤ p 3 := skip_composites (a := 89) (hp 3) (by omega) (by decide)
                                                  apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨19, 2, true, false⟩, ⟨97, 2, false, false⟩]
                                                  · unfold excluded; decide +kernel
                                                  · intro i; fin_cases i <;> simp [covers] <;> omega
              · have p2ge23 : 23 ≤ p 2 := skip_composites (a := 19) (hp 2) (by omega) (by decide)
                have p3ge29 : 29 ≤ p 3 := skip_composites (a := 23) (hp 3) (by omega) (by decide)
                by_cases h : p 2 = 23
                · by_cases h : e 0 = 2
                  · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨23, 2, true, false⟩, ⟨29, 2, false, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · by_cases h : p 3 = 29
                    · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨23, 2, true, false⟩, ⟨29, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · have p3ge31 : 31 ≤ p 3 := skip_composites (a := 29) (hp 3) (by omega) (by decide)
                      by_cases h : p 3 = 31
                      · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨23, 2, true, false⟩, ⟨31, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                        by_cases h : p 3 = 37
                        · by_cases h : e 1 = 2
                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨23, 2, true, false⟩, ⟨37, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨23, 2, true, false⟩, ⟨37, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                        · have p3ge41 : 41 ≤ p 3 := skip_composites (a := 37) (hp 3) (by omega) (by decide)
                          by_cases h : p 3 = 41
                          · by_cases h : e 1 = 2
                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨23, 2, true, false⟩, ⟨41, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                            · apply bad ![⟨3, 4, true, false⟩, ⟨5, 4, true, false⟩, ⟨23, 2, true, false⟩, ⟨41, 2, true, false⟩]
                              · unfold excluded; decide +kernel
                              · intro i; fin_cases i <;> simp [covers] <;> omega
                          · have p3ge43 : 43 ≤ p 3 := skip_composites (a := 41) (hp 3) (by omega) (by decide)
                            by_cases h : p 3 = 43
                            · by_cases h : e 1 = 2
                              · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨23, 2, true, false⟩, ⟨43, 2, true, false⟩]
                                · unfold excluded; decide +kernel
                                · intro i; fin_cases i <;> simp [covers] <;> omega
                              · by_cases h : e 0 = 4
                                · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨23, 2, true, false⟩, ⟨43, 2, true, false⟩]
                                  · unfold excluded; decide +kernel
                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨23, 2, true, false⟩, ⟨43, 2, true, false⟩]
                                  · unfold excluded; decide +kernel
                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                            · have p3ge47 : 47 ≤ p 3 := skip_composites (a := 43) (hp 3) (by omega) (by decide)
                              by_cases h : p 3 = 47
                              · by_cases h : e 1 = 2
                                · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨23, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                  · unfold excluded; decide +kernel
                                  · intro i; fin_cases i <;> simp [covers] <;> omega
                                · by_cases h : e 0 = 4
                                  · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨23, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                                  · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨23, 2, true, false⟩, ⟨47, 2, true, false⟩]
                                    · unfold excluded; decide +kernel
                                    · intro i; fin_cases i <;> simp [covers] <;> omega
                              · have p3ge53 : 53 ≤ p 3 := skip_composites (a := 47) (hp 3) (by omega) (by decide)
                                apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨23, 2, true, false⟩, ⟨53, 2, false, false⟩]
                                · unfold excluded; decide +kernel
                                · intro i; fin_cases i <;> simp [covers] <;> omega
                · have p2ge29 : 29 ≤ p 2 := skip_composites (a := 23) (hp 2) (by omega) (by decide)
                  have p3ge31 : 31 ≤ p 3 := skip_composites (a := 29) (hp 3) (by omega) (by decide)
                  by_cases h : p 2 = 29
                  · by_cases h : e 0 = 2
                    · apply bad ![⟨3, 2, true, true⟩, ⟨5, 2, true, false⟩, ⟨29, 2, true, false⟩, ⟨31, 2, false, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · by_cases h : p 3 = 31
                      · by_cases h : e 1 = 2
                        · apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, true⟩, ⟨29, 2, true, false⟩, ⟨31, 2, true, false⟩]
                          · unfold excluded; decide +kernel
                          · intro i; fin_cases i <;> simp [covers] <;> omega
                        · by_cases h : e 0 = 4
                          · apply bad ![⟨3, 4, true, true⟩, ⟨5, 4, true, false⟩, ⟨29, 2, true, false⟩, ⟨31, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · apply bad ![⟨3, 6, true, false⟩, ⟨5, 4, true, false⟩, ⟨29, 2, true, false⟩, ⟨31, 2, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                      · have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                        apply bad ![⟨3, 4, true, false⟩, ⟨5, 2, true, false⟩, ⟨29, 2, true, false⟩, ⟨37, 2, false, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                  · have p2ge31 : 31 ≤ p 2 := skip_composites (a := 29) (hp 2) (by omega) (by decide)
                    have p3ge37 : 37 ≤ p 3 := skip_composites (a := 31) (hp 3) (by omega) (by decide)
                    apply bad ![⟨3, 2, true, false⟩, ⟨5, 2, true, false⟩, ⟨31, 2, false, false⟩, ⟨37, 2, false, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
    · have p1ge7 : 7 ≤ p 1 := skip_composites (a := 5) (hp 1) (by omega) (by decide)
      have p2ge11 : 11 ≤ p 2 := skip_composites (a := 7) (hp 2) (by omega) (by decide)
      have p3ge13 : 13 ≤ p 3 := skip_composites (a := 11) (hp 3) (by omega) (by decide)
      by_cases h : p 1 = 7
      · by_cases h : p 2 = 11
        · by_cases h : p 3 = 13
          · by_cases h : e 0 = 2
            · by_cases h : e 1 = 2
              · by_cases h : e 2 = 2
                · by_cases h : e 3 = 2
                  · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, true⟩, ⟨11, 2, true, true⟩, ⟨13, 2, true, true⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, true⟩, ⟨11, 2, true, true⟩, ⟨13, 4, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, true⟩, ⟨11, 4, true, false⟩, ⟨13, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
              · apply bad ![⟨3, 2, true, true⟩, ⟨7, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨13, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
            · apply bad ![⟨3, 4, true, false⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨13, 2, true, false⟩]
              · unfold excluded; decide +kernel
              · intro i; fin_cases i <;> simp [covers] <;> omega
          · have p3ge17 : 17 ≤ p 3 := skip_composites (a := 13) (hp 3) (by omega) (by decide)
            by_cases h : p 3 = 17
            · by_cases h : e 0 = 2
              · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨17, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
              · apply bad ![⟨3, 4, true, false⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨17, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
            · have p3ge19 : 19 ≤ p 3 := skip_composites (a := 17) (hp 3) (by omega) (by decide)
              by_cases h : p 3 = 19
              · by_cases h : e 0 = 2
                · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨19, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
                · apply bad ![⟨3, 4, true, false⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨19, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
              · have p3ge23 : 23 ≤ p 3 := skip_composites (a := 19) (hp 3) (by omega) (by decide)
                by_cases h : p 3 = 23
                · by_cases h : e 0 = 2
                  · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨23, 2, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · by_cases h : e 0 = 4
                    · by_cases h : e 1 = 2
                      · apply bad ![⟨3, 4, true, true⟩, ⟨7, 2, true, true⟩, ⟨11, 2, true, false⟩, ⟨23, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · apply bad ![⟨3, 4, true, true⟩, ⟨7, 4, true, false⟩, ⟨11, 2, true, false⟩, ⟨23, 2, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                    · apply bad ![⟨3, 6, true, false⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨23, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                · have p3ge29 : 29 ≤ p 3 := skip_composites (a := 23) (hp 3) (by omega) (by decide)
                  apply bad ![⟨3, 2, true, false⟩, ⟨7, 2, true, false⟩, ⟨11, 2, true, false⟩, ⟨29, 2, false, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
        · have p2ge13 : 13 ≤ p 2 := skip_composites (a := 11) (hp 2) (by omega) (by decide)
          have p3ge17 : 17 ≤ p 3 := skip_composites (a := 13) (hp 3) (by omega) (by decide)
          by_cases h : p 2 = 13
          · by_cases h : p 3 = 17
            · by_cases h : e 0 = 2
              · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨17, 2, true, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
              · by_cases h : e 0 = 4
                · by_cases h : e 1 = 2
                  · by_cases h : e 2 = 2
                    · apply bad ![⟨3, 4, true, true⟩, ⟨7, 2, true, true⟩, ⟨13, 2, true, true⟩, ⟨17, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · by_cases h : e 3 = 2
                      · apply bad ![⟨3, 4, true, true⟩, ⟨7, 2, true, true⟩, ⟨13, 4, true, false⟩, ⟨17, 2, true, true⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                      · apply bad ![⟨3, 4, true, true⟩, ⟨7, 2, true, true⟩, ⟨13, 4, true, false⟩, ⟨17, 4, true, false⟩]
                        · unfold excluded; decide +kernel
                        · intro i; fin_cases i <;> simp [covers] <;> omega
                  · apply bad ![⟨3, 4, true, true⟩, ⟨7, 4, true, false⟩, ⟨13, 2, true, false⟩, ⟨17, 2, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                · apply bad ![⟨3, 6, true, false⟩, ⟨7, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨17, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
            · have p3ge19 : 19 ≤ p 3 := skip_composites (a := 17) (hp 3) (by omega) (by decide)
              by_cases h : p 3 = 19
              · by_cases h : e 0 = 2
                · apply bad ![⟨3, 2, true, true⟩, ⟨7, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨19, 2, true, false⟩]
                  · unfold excluded; decide +kernel
                  · intro i; fin_cases i <;> simp [covers] <;> omega
                · by_cases h : e 0 = 4
                  · apply bad ![⟨3, 4, true, true⟩, ⟨7, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨19, 2, true, false⟩]
                    · unfold excluded; decide +kernel
                    · intro i; fin_cases i <;> simp [covers] <;> omega
                  · by_cases h : e 1 = 2
                    · apply bad ![⟨3, 6, true, false⟩, ⟨7, 2, true, true⟩, ⟨13, 2, true, false⟩, ⟨19, 2, true, false⟩]
                      · unfold excluded; decide +kernel
                      · intro i; fin_cases i <;> simp [covers] <;> omega
                    · by_cases h : e 0 = 6
                      · by_cases h : e 2 = 2
                        · apply bad ![⟨3, 6, true, true⟩, ⟨7, 4, true, false⟩, ⟨13, 2, true, true⟩, ⟨19, 2, true, false⟩]
                          · unfold excluded; decide +kernel
                          · intro i; fin_cases i <;> simp [covers] <;> omega
                        · by_cases h : e 3 = 2
                          · apply bad ![⟨3, 6, true, true⟩, ⟨7, 4, true, false⟩, ⟨13, 4, true, false⟩, ⟨19, 2, true, true⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · apply bad ![⟨3, 6, true, true⟩, ⟨7, 4, true, false⟩, ⟨13, 4, true, false⟩, ⟨19, 4, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                      · by_cases h : e 2 = 2
                        · by_cases h : e 3 = 2
                          · apply bad ![⟨3, 8, true, false⟩, ⟨7, 4, true, false⟩, ⟨13, 2, true, true⟩, ⟨19, 2, true, true⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                          · apply bad ![⟨3, 8, true, false⟩, ⟨7, 4, true, false⟩, ⟨13, 2, true, true⟩, ⟨19, 4, true, false⟩]
                            · unfold excluded; decide +kernel
                            · intro i; fin_cases i <;> simp [covers] <;> omega
                        · apply bad ![⟨3, 8, true, false⟩, ⟨7, 4, true, false⟩, ⟨13, 4, true, false⟩, ⟨19, 2, true, false⟩]
                          · unfold excluded; decide +kernel
                          · intro i; fin_cases i <;> simp [covers] <;> omega
              · have p3ge23 : 23 ≤ p 3 := skip_composites (a := 19) (hp 3) (by omega) (by decide)
                apply bad ![⟨3, 2, true, false⟩, ⟨7, 2, true, false⟩, ⟨13, 2, true, false⟩, ⟨23, 2, false, false⟩]
                · unfold excluded; decide +kernel
                · intro i; fin_cases i <;> simp [covers] <;> omega
          · have p2ge17 : 17 ≤ p 2 := skip_composites (a := 13) (hp 2) (by omega) (by decide)
            have p3ge19 : 19 ≤ p 3 := skip_composites (a := 17) (hp 3) (by omega) (by decide)
            apply bad ![⟨3, 2, true, false⟩, ⟨7, 2, true, false⟩, ⟨17, 2, false, false⟩, ⟨19, 2, false, false⟩]
            · unfold excluded; decide +kernel
            · intro i; fin_cases i <;> simp [covers] <;> omega
      · have p1ge11 : 11 ≤ p 1 := skip_composites (a := 7) (hp 1) (by omega) (by decide)
        have p2ge13 : 13 ≤ p 2 := skip_composites (a := 11) (hp 2) (by omega) (by decide)
        have p3ge17 : 17 ≤ p 3 := skip_composites (a := 13) (hp 3) (by omega) (by decide)
        apply bad ![⟨3, 2, true, false⟩, ⟨11, 2, false, false⟩, ⟨13, 2, false, false⟩, ⟨17, 2, false, false⟩]
        · unfold excluded; decide +kernel
        · intro i; fin_cases i <;> simp [covers] <;> omega
  · have p0ge5 : 5 ≤ p 0 := skip_composites (a := 3) (hp 0) (by omega) (by decide)
    have p1ge7 : 7 ≤ p 1 := skip_composites (a := 5) (hp 1) (by omega) (by decide)
    have p2ge11 : 11 ≤ p 2 := skip_composites (a := 7) (hp 2) (by omega) (by decide)
    have p3ge13 : 13 ≤ p 3 := skip_composites (a := 11) (hp 3) (by omega) (by decide)
    apply bad ![⟨5, 2, false, false⟩, ⟨7, 2, false, false⟩, ⟨11, 2, false, false⟩, ⟨13, 2, false, false⟩]
    · unfold excluded; decide +kernel
    · intro i; fin_cases i <;> simp [covers] <;> omega

/-- No odd almost-perfect square has exactly four distinct prime divisors. -/
theorem no_odd_almost_perfect_four {n : ℕ} (hn : 0 < n) (ho : Odd n) (hs : IsSquare n)
    (hc : n.primeFactors.card = 4) : 1 + σ 1 n ≠ 2 * n := by
  classical
  intro he
  let p : Fin 4 → ℕ := n.primeFactors.orderEmbOfFin hc
  let e : Fin 4 → ℕ := fun i => n.factorization (p i)
  have hm (i : Fin 4) : p i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem hc i
  have hp (i : Fin 4) : (p i).Prime := Nat.prime_of_mem_primeFactors (hm i)
  have hd (i : Fin 4) : p i ∣ n := Nat.dvd_of_mem_primeFactors (hm i)
  have hodd (i : Fin 4) : Odd (p i) := (hp i).odd_of_ne_two fun h => ho.not_two_dvd_nat (h ▸ hd i)
  have heven (i : Fin 4) : Even (e i) := Nat.isSquare_iff_even_factorization.mp hs _ (hp i)
  have hpos (i : Fin 4) : 0 < e i := (hp i).factorization_pos_of_dvd hn.ne' (hd i)
  have reindex (f : ℕ → ℚ) : (∏ i, f (p i)) = ∏ q ∈ n.primeFactors, f q := by
    calc
      _ = ∏ q : n.primeFactors, f (q : ℕ) :=
        Fintype.prod_equiv (n.primeFactors.orderIsoOfFin hc).toEquiv _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort n.primeFactors f
  have hden : (∏ i, (p i : ℚ) ^ e i) = n := by
    change (∏ i, (p i : ℚ) ^ n.factorization (p i)) = n
    rw [reindex (fun q : ℕ => (q : ℚ) ^ n.factorization q)]
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  have hrat : (∏ i, localRatio (p i) (e i)) = (σ 1 n : ℚ) / n := by
    change (∏ i, localRatio (p i) (n.factorization (p i))) = _
    rw [reindex (fun q => localRatio q (n.factorization q)), sigma_ratio_eq_prod hn]
  have hnat : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have eq : 1 + (σ 1 n : ℚ) = 2 * n := by exact_mod_cast he
  apply four_intervals p e hp hodd (n.primeFactors.orderEmbOfFin hc).strictMono heven hpos
  rw [hden, hrat, ← add_div]
  exact (div_eq_iff hnat).mpr (by linarith)

end OMA.OddAlmost

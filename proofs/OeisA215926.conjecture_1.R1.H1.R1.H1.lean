import OMAReductions.R_OeisA215926_conjecture_1_R1_H1_R1

/-!
For an odd square with at most three distinct prime divisors, each prime-power
divisor ratio lies in an explicit interval. The product is either at most
255/128 or at least two, whereas the ratio of an almost perfect number
greater than 128 is strictly between these bounds.
-/

namespace OMA.OddAlmost

open Finset

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

end OMA.OddAlmost

namespace OMA.OddAlmost

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

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

/-- Only the exponent at three needs two separate intervals. The last
interval covers all primes at least seventeen. -/
private def band (p e : ℕ) : Fin 7 :=
  if p = 3 then (if e = 2 then 0 else 1) else if p = 5 then 2
  else if p = 7 then 3 else if p = 11 then 4 else if p = 13 then 5 else 6

private def key : Fin 7 → ℕ := ![3, 3, 5, 7, 11, 13, 17]
private def lower : Fin 7 → ℚ := ![13/9, 121/81, 31/25, 57/49, 133/121, 183/169, 1]
private def upper : Fin 7 → ℚ := ![13/9, 3/2, 5/4, 7/6, 11/10, 13/12, 17/16]

private theorem prime_cases {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ 17 ≤ p := by
  by_cases h : 17 ≤ p
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · have cert : ∀ j : Fin 17, j.val.Prime → Odd j.val →
        j.val = 3 ∨ j.val = 5 ∨ j.val = 7 ∨ j.val = 11 ∨ j.val = 13 ∨ 17 ≤ j.val := by decide
    exact cert ⟨p, by omega⟩ hp ho

private theorem prime_key {p e : ℕ} (hp : p.Prime) (ho : Odd p) :
    key (band p e) = min p 17 := by
  rcases prime_cases hp ho with rfl | rfl | rfl | rfl | rfl | h
  · by_cases he : e = 2 <;> simp [key, band, he]
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [key, band, show p ≠ 3 by omega, show p ≠ 5 by omega, show p ≠ 7 by omega,
      show p ≠ 11 by omega, show p ≠ 13 by omega, min_eq_right h]

private theorem prime_interval {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : Even e)
    (hpos : 0 < e) :
    lower (band p e) ≤ localRatio p e ∧ localRatio p e ≤ upper (band p e) := by
  obtain ⟨t, ht⟩ := he
  have he2 : 2 ≤ e := by omega
  rcases prime_cases hp ho with rfl | rfl | rfl | rfl | rfl | h
  · by_cases h : e = 2
    · subst e
      norm_num [band, lower, upper, localRatio, sum_range_succ]
    · have h4 : 4 ≤ e := by omega
      constructor
      · convert localRatio_mono (p := 3) (by decide) h4 using 1 <;>
          norm_num [band, lower, h, localRatio, sum_range_succ]
      · convert localRatio_upper (p := 3) (e := e) (by decide) using 1 <;>
          norm_num [band, upper, h, factorBound]
  · constructor
    · convert localRatio_mono (p := 5) (by decide) he2 using 1 <;>
        norm_num [band, lower, localRatio, sum_range_succ]
    · convert localRatio_upper (p := 5) (e := e) (by decide) using 1 <;>
        norm_num [band, upper, factorBound]
  · constructor
    · convert localRatio_mono (p := 7) (by decide) he2 using 1 <;>
        norm_num [band, lower, localRatio, sum_range_succ]
    · convert localRatio_upper (p := 7) (e := e) (by decide) using 1 <;>
        norm_num [band, upper, factorBound]
  · constructor
    · convert localRatio_mono (p := 11) (by decide) he2 using 1 <;>
        norm_num [band, lower, localRatio, sum_range_succ]
    · convert localRatio_upper (p := 11) (e := e) (by decide) using 1 <;>
        norm_num [band, upper, factorBound]
  · constructor
    · convert localRatio_mono (p := 13) (by decide) he2 using 1 <;>
        norm_num [band, lower, localRatio, sum_range_succ]
    · convert localRatio_upper (p := 13) (e := e) (by decide) using 1 <;>
        norm_num [band, upper, factorBound]
  · have hb : band p e = 6 := by
      simp [band, show p ≠ 3 by omega, show p ≠ 5 by omega, show p ≠ 7 by omega,
        show p ≠ 11 by omega, show p ≠ 13 by omega]
    rw [hb]
    constructor
    · convert localRatio_mono hp.pos (Nat.zero_le e) using 1 <;> simp [lower, localRatio]
    · apply (localRatio_upper hp.two_le).trans
      have hu := factorBound_antitone (by decide : 2 ≤ 17) h
      convert hu using 1 <;> norm_num [upper, factorBound]

private def compatible (i j : Fin 7) : Prop := key i = 17 ∨ key j = 17 ∨ key i ≠ key j

private theorem prime_compatible {p q e f : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (hqo : Odd q) (hne : p ≠ q) :
    compatible (band p e) (band q f) := by
  unfold compatible
  rw [prime_key hp hpo, prime_key hq hqo]
  omega

/-- Exact rational certificates for all possible triples of prime bands. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem triple_intervals (a b c : Fin 7)
    (hab : compatible a b) (hac : compatible a c) (hbc : compatible b c) :
    upper a * upper b * upper c ≤ 255/128 ∨ 2 ≤ lower a * lower b * lower c := by
  have cert : ∀ a b c : Fin 7, (key a = 17 ∨ key b = 17 ∨ key a ≠ key b) →
      (key a = 17 ∨ key c = 17 ∨ key a ≠ key c) →
      (key b = 17 ∨ key c = 17 ∨ key b ≠ key c) →
      upper a * upper b * upper c ≤ 255/128 ∨ 2 ≤ lower a * lower b * lower c := by decide
  exact cert a b c hab hac hbc

private theorem ratio_outside {n : ℕ} (hn : 0 < n) (ho : Odd n) (hs : IsSquare n)
    (hc : n.primeFactors.card ≤ 3) :
    (σ 1 n : ℚ) / n ≤ 255/128 ∨ 2 ≤ (σ 1 n : ℚ) / n := by
  let B := fun p => band p (n.factorization p)
  let R := fun p => localRatio p (n.factorization p)
  have hprime (p : ℕ) (h : p ∈ n.primeFactors) : p.Prime ∧ Odd p := by
    have hp := Nat.prime_of_mem_primeFactors h
    have hd := Nat.dvd_of_mem_primeFactors h
    exact ⟨hp, hp.odd_of_ne_two (fun h2 => ho.not_two_dvd_nat (h2 ▸ hd))⟩
  have interval (p : ℕ) (h : p ∈ n.primeFactors) : lower (B p) ≤ R p ∧ R p ≤ upper (B p) :=
    prime_interval (hprime p h).1 (hprime p h).2
      (Nat.isSquare_iff_even_factorization.mp hs p (hprime p h).1)
      ((hprime p h).1.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors h))
  have comp (p q : ℕ) (h : p ∈ n.primeFactors) (h' : q ∈ n.primeFactors) (hne : p ≠ q) :
      compatible (B p) (B q) :=
    prime_compatible (hprime p h).1 (hprime p h).2 (hprime q h').1 (hprime q h').2 hne
  have lo : ∀ i : Fin 7, 0 ≤ lower i := by decide
  have up : ∀ i : Fin 7, 0 ≤ upper i := by decide
  have nonneg (p : ℕ) : 0 ≤ R p := localRatio_nonneg p _
  by_cases h0 : n.primeFactors.card = 0
  · left
    rw [sigma_ratio_eq_prod hn, card_eq_zero.mp h0, prod_empty]
    norm_num
  by_cases h1 : n.primeFactors.card = 1
  · obtain ⟨a, hset⟩ := card_eq_one.mp h1
    have ha : a ∈ n.primeFactors := by simp [hset]
    have hprod : (σ 1 n : ℚ) / n = R a := by simp [sigma_ratio_eq_prod hn, hset, R]
    have cert : ∀ i : Fin 7, upper i ≤ 255/128 := by decide
    left
    rw [hprod]
    exact (interval a ha).2.trans (cert _)
  by_cases h2 : n.primeFactors.card = 2
  · obtain ⟨a, b, hab, hset⟩ := card_eq_two.mp h2
    have ha : a ∈ n.primeFactors := by simp [hset]
    have hb : b ∈ n.primeFactors := by simp [hset]
    have hprod : (σ 1 n : ℚ) / n = R a * R b := by simp [sigma_ratio_eq_prod hn, hset, R, hab]
    have cert : ∀ i j : Fin 7, (key i = 17 ∨ key j = 17 ∨ key i ≠ key j) →
        upper i * upper j ≤ 255/128 := by decide
    left
    rw [hprod]
    exact (mul_le_mul (interval a ha).2 (interval b hb).2 (nonneg b) (up _)).trans
      (cert _ _ (comp a b ha hb hab))
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ :=
    card_eq_three.mp (show n.primeFactors.card = 3 by omega)
  have ha : a ∈ n.primeFactors := by simp [hset]
  have hb : b ∈ n.primeFactors := by simp [hset]
  have hc' : c ∈ n.primeFactors := by simp [hset]
  have hprod : (σ 1 n : ℚ) / n = R a * R b * R c := by
    rw [sigma_ratio_eq_prod hn, hset]
    simp [R, hab, hac, hbc, mul_assoc]
  rw [hprod]
  rcases triple_intervals (B a) (B b) (B c) (comp _ _ ha hb hab)
      (comp _ _ ha hc' hac) (comp _ _ hb hc' hbc) with large | small
  · left
    exact (mul_le_mul (mul_le_mul (interval _ ha).2 (interval _ hb).2
      (nonneg b) (up _)) (interval _ hc').2 (nonneg c) (mul_nonneg (up _) (up _))).trans large
  · right
    exact small.trans (mul_le_mul (mul_le_mul (interval _ ha).1 (interval _ hb).1
      (lo _) (nonneg a)) (interval _ hc').1 (lo _) (mul_nonneg (nonneg _) (nonneg _)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem at_least_four {n : ℕ} (hn : 1 < n) (ho : Odd n) (hs : IsSquare n)
    (he : 1 + σ 1 n = 2 * n) : 4 ≤ n.primeFactors.card := by
  by_contra! hc
  have small : ∀ j : Fin 129, 1 < j.val → Odd j.val →
      1 + σ 1 j.val ≠ 2 * j.val := by decide
  by_cases h : n ≤ 128
  · exact small ⟨n, by omega⟩ hn ho he
  have hq : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hge : (128 : ℚ) < n := by exact_mod_cast (by omega : 128 < n)
  have heq : 1 + (σ 1 n : ℚ) = 2 * n := by exact_mod_cast he
  rcases ratio_outside (by omega : 0 < n) ho hs (by omega) with low | high
  · have := (div_le_iff₀ hq).mp low
    linarith
  · have := (le_div_iff₀ hq).mp high
    linarith

end OMA.OddAlmost

theorem OMA.solution : OMA.R_OeisA215926_conjecture_1_R1_H1_R1.H1 := by
  intro m ho hn hc he
  have hs : IsSquare (m ^ 2) := ⟨m, by rw [pow_two]⟩
  have hk := OMA.OddAlmost.at_least_four hn ho.pow hs he
  rw [Nat.primeFactors_pow m (by decide : (2 : ℕ) ≠ 0)] at hk
  omega

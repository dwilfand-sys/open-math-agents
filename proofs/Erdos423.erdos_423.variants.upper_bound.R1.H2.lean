import OMAReductions.R_Erdos423_erdos_423_variants_upper_bound_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset BigOperators

namespace OMA.HofstadterCounting

/-- Once the right endpoint of a block is available, its sum is a candidate that
the greedy rule cannot jump over. Its first occurrence is after that endpoint. -/
lemma block_occurs_after {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + 1 ≤ j) :
    ∃ k : ℕ, j < k ∧ a k = ∑ l ∈ Finset.Icc i j, a l := by
  let s := ∑ l ∈ Finset.Icc i j, a l
  change ∃ k : ℕ, j < k ∧ a k = s
  have hpair : ({i, j} : Finset ℕ) ⊆ Finset.Icc i j := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : a i + a j ≤ s := by
    calc
      a i + a j = ∑ l ∈ ({i, j} : Finset ℕ), a l :=
        (Finset.sum_pair (show i ≠ j by omega)).symm
      _ ≤ s := Finset.sum_le_sum_of_subset_of_nonneg hpair (fun _ _ _ => Nat.zero_le _)
  have hi_pos := ha.le_apply i hi
  have hstart : a j < s := by omega
  by_contra hnever
  have step (k : ℕ) (hk : j ≤ k) (hbefore : a k < s) : a (k + 1) < s := by
    by_contra! hpast
    have hne : a (k + 1) ≠ s := fun heq => hnever ⟨k + 1, by omega, heq⟩
    have hstrict : s < a (k + 1) := lt_of_le_of_ne hpast hne.symm
    have hgap := (ha.2.2 (k + 1) (by omega)).2.2 s (by simpa using hbefore) hstrict
    exact hgap ⟨i, j, hi, hij, by omega, rfl⟩
  have below : ∀ k : ℕ, j ≤ k → a k < s := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hstart
    | succ k hk ih => exact step k hk ih
  have hlow := below (j + s) (by omega)
  have hhigh := ha.le_apply (j + s) (by omega)
  omega

/-- If the first m terms generate n distinct block sums, the n-th term is at
most the sum of the whole prefix. The arbitrary value a 0 is excluded. -/
lemma term_le_prefix_of_block_count {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a)
    {n m : ℕ} (hn : 1 ≤ n)
    (hcount : n ≤ ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard) :
    a n ≤ ∑ l ∈ Finset.Icc 1 m, a l := by
  classical
  by_contra! htoo
  let A := (Finset.Icc 1 (n - 1)).image a
  have hcontained : {s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s} ⊆
      (A : Set ℕ) := by
    intro s hs
    obtain ⟨i, j, hi, hij, hjm, hsum⟩ := hs
    obtain ⟨k, hjk, hvalue⟩ := block_occurs_after ha hi hij
    have hbound : s ≤ ∑ l ∈ Finset.Icc 1 m, a l := by
      rw [hsum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        obtain ⟨hil, hlj⟩ := Finset.mem_Icc.mp hl
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · exact fun _ _ _ => Nat.zero_le _
    have hvalue' : a k = s := hvalue.trans hsum.symm
    have hkn : k < n :=
      (Erdos423.IsHofstadterSeq.lt_iff_lt ha (by omega : 1 ≤ k) hn).1
        (by rw [hvalue']; exact lt_of_le_of_lt hbound htoo)
    change s ∈ (Finset.Icc 1 (n - 1)).image a
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hvalue'⟩
  have hcard : ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard ≤ A.card := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcontained A.finite_toSet
  have hsize : A.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_image_le
  rw [Nat.card_Icc] at hsize
  omega

/-- Form of the counting bound suited to a recurrence in the index. -/
lemma term_le_mul_of_block_count {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a)
    {n m : ℕ} (hn : 1 ≤ n)
    (hcount : n ≤ ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard) :
    a n ≤ m * a m := by
  calc
    a n ≤ ∑ l ∈ Finset.Icc 1 m, a l := term_le_prefix_of_block_count ha hn hcount
    _ ≤ ∑ _l ∈ Finset.Icc 1 m, a m := by
      apply Finset.sum_le_sum
      intro l hl
      obtain ⟨hl1, hlm⟩ := Finset.mem_Icc.mp hl
      rcases eq_or_lt_of_le hlm with rfl | hlt
      · exact le_rfl
      · exact ((Erdos423.IsHofstadterSeq.lt_iff_lt ha hl1 (by omega)).2 hlt).le
    _ = m * a m := by simp [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]

end OMA.HofstadterCounting

open Filter

namespace Erdos423Work

/-- A superlinear count of distinct objects supplies a smaller index with enough objects.
The floor keeps the comparison with the induction scale free of multiplicative constants. -/
theorem floor_cutoff_of_count_growth (B : ℕ → ℕ) {c d : ℝ} (hc : 1 < c)
    (hd : 1 / (c - 1) < d)
    (hg : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ (c - η) ≤ C * (B m : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ n ≤ B m ∧
      (m : ℝ) ≤ (n : ℝ) ^ (d / (d + 1)) := by
  have hc' : 0 < c - 1 := by linarith
  have hd' : 0 < d := lt_trans (one_div_pos.mpr hc') hd
  have hden : 0 < d + 1 := by linarith
  let p := d / (d + 1)
  have hp : 0 < p := div_pos hd' hden
  have hp_lt : p < 1 := (div_lt_iff₀ hden).2 (by linarith)
  have hpc : 1 < p * c := by
    have hdc := (div_lt_iff₀ hc').mp hd
    calc
      1 < d * c / (d + 1) := (lt_div_iff₀ hden).2 (by nlinarith)
      _ = p * c := by dsimp only [p]; ring
  -- Choose q = c - η so that p*q is exactly halfway between 1 and p*c.
  let η := (p * c - 1) / (2 * p)
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  let q := c - η
  have hpq_eq : p * q = (p * c + 1) / 2 := by
    dsimp only [q, η]
    field_simp [ne_of_gt hp] <;> ring
  have hpq : 1 < p * q := by linarith
  have hq : 0 < q := by
    by_contra! hnq
    have := mul_nonpos_of_nonneg_of_nonpos hp.le hnq
    linarith
  obtain ⟨C, hC, hcount⟩ := hg η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hcount
  have htendsto (t : ℝ) (ht : 0 < t) :
      Tendsto (fun n : ℕ => (n : ℝ) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop
  have htwo : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have hK : 0 < (2 : ℝ) ^ q * C := mul_pos htwo hC
  filter_upwards [eventually_gt_atTop (1 : ℕ), (htendsto p hp).eventually_ge_atTop 2,
    (htendsto p hp).eventually_ge_atTop (N : ℝ),
    (htendsto (p * q - 1) (by linarith)).eventually_ge_atTop ((2 : ℝ) ^ q * C)]
    with n hn h2 hNn hlarge
  change (2 : ℝ) ≤ (n : ℝ) ^ p at h2
  change (N : ℝ) ≤ (n : ℝ) ^ p at hNn
  change (2 : ℝ) ^ q * C ≤ (n : ℝ) ^ (p * q - 1) at hlarge
  let m : ℕ := ⌊(n : ℝ) ^ p⌋₊
  have hnreal : 1 < (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hm : 1 ≤ m := (Nat.one_le_floor_iff _).2 (by linarith)
  have hmN : N ≤ m := Nat.le_floor hNn
  have hmreal : (m : ℝ) ≤ (n : ℝ) ^ p := Nat.floor_le (Real.rpow_nonneg hnpos.le p)
  have hmn_real : (m : ℝ) < (n : ℝ) := calc
    (m : ℝ) ≤ (n : ℝ) ^ p := hmreal
    _ < (n : ℝ) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hnreal hp_lt
    _ = (n : ℝ) := Real.rpow_one _
  have hmn : m < n := by exact_mod_cast hmn_real
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : (n : ℝ) ^ p < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdouble : (n : ℝ) ^ p ≤ 2 * (m : ℝ) := by linarith
  have hB : (m : ℝ) ^ q ≤ C * (B m : ℝ) := hN m hmN
  have hscaled : ((2 : ℝ) ^ q * C) * (n : ℝ) ≤ ((2 : ℝ) ^ q * C) * (B m : ℝ) := calc
    ((2 : ℝ) ^ q * C) * (n : ℝ) ≤ (n : ℝ) ^ (p * q - 1) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge hnpos.le
    _ = (n : ℝ) ^ (p * q) := by
      rw [← Real.rpow_add_one hnpos.ne', sub_add_cancel]
    _ = ((n : ℝ) ^ p) ^ q := Real.rpow_mul hnpos.le p q
    _ ≤ (2 * (m : ℝ)) ^ q :=
      Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le p) hdouble hq.le
    _ = (2 : ℝ) ^ q * (m : ℝ) ^ q := Real.mul_rpow (by norm_num) (by positivity)
    _ ≤ (2 : ℝ) ^ q * (C * (B m : ℝ)) := mul_le_mul_of_nonneg_left hB htwo.le
    _ = ((2 : ℝ) ^ q * C) * (B m : ℝ) := (mul_assoc _ _ _).symm
  have hnB_real : (n : ℝ) ≤ (B m : ℝ) := le_of_not_gt fun hlt =>
    (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_left hlt hK)
  exact ⟨m, hm, hmn, by exact_mod_cast hnB_real, hmreal⟩

end Erdos423Work

open Filter Asymptotics

namespace Erdos423

/-- If each sufficiently late term is bounded by the product of a smaller index
and its term, an upper bound on that index propagates a polynomial growth bound. -/
theorem isBigO_rpow_of_smaller_index (a : ℕ → ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hstep : ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, 1 ≤ m ∧ m < n ∧
      a n ≤ m * a m ∧ (m : ℝ) ≤ (n : ℝ) ^ (d / (d + 1))) :
    (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ d) := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hstep
  let K : ℕ := (Finset.range N).sup a
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hd1 : 0 < d + 1 := by linarith
  have bound (n : ℕ) : 1 ≤ n → (a n : ℝ) ≤ (K : ℝ) * (n : ℝ) ^ d := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hnN : N ≤ n
      · obtain ⟨m, hm, hmn, hrec, hindex⟩ := hN n hnN
        have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
        have hpower : (m : ℝ) ^ (d + 1) ≤ (n : ℝ) ^ d := calc
          (m : ℝ) ^ (d + 1) ≤ ((n : ℝ) ^ (d / (d + 1))) ^ (d + 1) :=
            Real.rpow_le_rpow hmR.le hindex hd1.le
          _ = (n : ℝ) ^ d := by
            rw [← Real.rpow_mul (Nat.cast_nonneg n), div_mul_cancel₀ d hd1.ne']
        calc
          (a n : ℝ) ≤ (m : ℝ) * (a m : ℝ) := by exact_mod_cast hrec
          _ ≤ (m : ℝ) * ((K : ℝ) * (m : ℝ) ^ d) :=
            mul_le_mul_of_nonneg_left (ih m hmn hm) hmR.le
          _ = (K : ℝ) * (m : ℝ) ^ (d + 1) := by
            rw [Real.rpow_add_one hmR.ne']
            ring
          _ ≤ (K : ℝ) * (n : ℝ) ^ d := mul_le_mul_of_nonneg_left hpower hK
      · have hsmall : a n ≤ K :=
          Finset.le_sup (f := a) (Finset.mem_range.mpr (by omega : n < N))
        have hlarge : (1 : ℝ) ≤ (n : ℝ) ^ d :=
          Real.one_le_rpow (by exact_mod_cast hn) hd
        calc
          (a n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hsmall
          _ = (K : ℝ) * 1 := (mul_one _).symm
          _ ≤ (K : ℝ) * (n : ℝ) ^ d := mul_le_mul_of_nonneg_left hlarge hK
  refine Asymptotics.isBigO_iff.mpr ⟨(K : ℝ), ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  change ‖(a n : ℝ)‖ ≤ (K : ℝ) * ‖(n : ℝ) ^ d‖
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (a n)),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) d)] using bound n hn

end Erdos423

theorem OMA.solution : OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H2 := by
  intro a ha c hc hcount ε hε
  let d : ℝ := 1 / (c - 1) + ε
  have hpositive : 0 < 1 / (c - 1) := one_div_pos.mpr (sub_pos.mpr hc)
  have hd : 1 / (c - 1) < d := by dsimp [d]; linarith
  have hnonneg : 0 ≤ d := (lt_trans hpositive hd).le
  let B : ℕ → ℕ := fun m => ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard
  have hcut := Erdos423Work.floor_cutoff_of_count_growth B hc hd hcount
  apply Erdos423.isBigO_rpow_of_smaller_index a hnonneg
  filter_upwards [hcut, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  obtain ⟨m, hm, hmn, hcard, hpow⟩ := hn
  exact ⟨m, hm, hmn, OMA.HofstadterCounting.term_le_mul_of_block_count ha hnpos hcard, hpow⟩

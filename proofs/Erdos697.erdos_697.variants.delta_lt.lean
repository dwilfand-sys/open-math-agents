import FormalConjectures.ErdosProblems.«697»
import Mathlib


/-!
# A strict upper bound for the divisibility density in Erdős 697

Each eligible divisor is of the form 1 + k m. Summing the individual
densities bounds the density of their union. The resulting finite harmonic
sum is strictly less than (m^α + 1)/m.

The periodic-density argument is reproduced from VinnyMo's accepted proof
of Erdos697.density_exists (PR 752). That argument generalizes the periodic
counting lemma developed by GMoney4362 for Erdős 859.
-/

namespace Erdos697Delta

open Filter
open scoped Topology

private lemma periodicDensity {p : ℕ → Prop} {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) :
    ∃ δ : ℝ, {n : ℕ | p n}.HasDensity δ := by
  classical
  let count := Nat.count p
  let density : ℝ := (count d : ℝ) / (d : ℝ)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 ≤ density := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hdensity_le : density ≤ 1 := by
    apply (div_le_one hd').mpr
    exact_mod_cast Nat.count_le (p := p) (n := d)
  have hshift (n : ℕ) : Nat.count (fun i ↦ p (i + d)) n = count n := by
    change Nat.count (fun i ↦ p (i + d)) n = Nat.count p n
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [Finset.mem_filter, hp i]
  have hblocks (q r : ℕ) : count (q * d + r) = q * count d + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * d + r) = (q + 1) * count d + count r
      rw [Nat.succ_mul, add_right_comm (q * d) d r, Nat.count_add', hshift]
      change count (q * d + r) + count d = (q + 1) * count d + count r
      rw [ih, Nat.succ_mul, add_right_comm]
  have hncard (n : ℕ) : ({m : ℕ | p m} ∩ Set.Iio n).ncard = count n := by
    rw [show {m : ℕ | p m} ∩ Set.Iio n =
        (↑((Finset.range n).filter p) : Set ℕ) by ext m; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  have herr : ∀ᶠ n : ℕ in atTop, |(count n : ℝ) / (n : ℝ) - density| ≤ (d : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let r := n % d
    let q := n / d
    have hsplit : q * d + r = n := by simpa [q, r, mul_comm] using Nat.div_add_mod n d
    have hcount : q * count d + count r = count n := (hblocks q r).symm.trans (congrArg count hsplit)
    have hsplit' : (q : ℝ) * (d : ℝ) + (r : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    have hcount' : (q : ℝ) * (count d : ℝ) + (count r : ℝ) = (count n : ℝ) := by
      exact_mod_cast hcount
    have hd_mul : (d : ℝ) * density = (count d : ℝ) :=
      mul_div_cancel₀ _ hd'.ne'
    have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn).bot_lt
    have hr : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt n hd).le
    have hcount_r : (count r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.count_le (p := p)
    have herror : (count n : ℝ) / (n : ℝ) - density =
        ((count r : ℝ) - (r : ℝ) * density) / (n : ℝ) := by
      apply (eq_div_iff hn'.ne').mpr
      calc
        _ = (count n : ℝ) - (n : ℝ) * density := by field_simp
        _ = _ := by rw [← hcount', ← hsplit', add_mul, mul_assoc, hd_mul]; ring
    rw [herror, abs_div, abs_of_pos hn']
    apply div_le_div_of_nonneg_right _ hn'.le
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left hdensity_le (Nat.cast_nonneg r)
      linarith [Nat.cast_nonneg (α := ℝ) (count r)]
    · have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hdensity
      linarith
  have ht : Tendsto (fun n : ℕ ↦ (count n : ℝ) / (n : ℝ) - density) atTop (𝓝 0) := by
    have hu := tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
    have hl : Tendsto (fun n : ℕ ↦ -((d : ℝ) / n)) atTop (𝓝 0) := by
      simpa only [neg_zero] using hu.neg
    refine hl.squeeze' hu ?_ ?_
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).1
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).2
  refine ⟨density, ?_⟩
  simpa [Set.HasDensity, Set.partialDensity, hncard] using ht.add_const density

private theorem existsDensityChecked : type_of% @Erdos697.density_exists := by
  intro m α
  let B := Real.exp ((m : ℝ) ^ α)
  let T := (⌈B⌉₊).factorial
  have divides_period {d : ℕ} (hd : (d : ℝ) ∈ Set.Ioo 1 B) : d ∣ T := by
    have hpos : 0 < (d : ℝ) := lt_trans zero_lt_one hd.1
    exact Nat.dvd_factorial (by exact_mod_cast hpos) (Nat.lt_ceil.mpr hd.2).le
  apply periodicDensity (d := T) (Nat.factorial_pos _)
  intro n
  apply propext
  constructor
  · rintro ⟨d, hmod, hd, hsum⟩
    exact ⟨d, hmod, hd, (Nat.dvd_add_iff_left (divides_period hd)).mpr hsum⟩
  · rintro ⟨d, hmod, hd, hn⟩
    exact ⟨d, hmod, hd, Nat.dvd_add hn (divides_period hd)⟩

end Erdos697Delta

open Filter
open scoped Topology

namespace Erdos697Bound

/-- On an interval whose length is a common multiple of the divisors, each divisor
contributes at most its exact reciprocal to the proportion covered by the union. -/
private theorem partial_density_common_multiple {S : Set ℕ} (I : Finset ℕ) (d : ℕ → ℕ)
    (hd : ∀ k ∈ I, 0 < d k) (cover : ∀ x ∈ S, ∃ k ∈ I, d k ∣ x)
    {N : ℕ} (hN : 0 < N) (common : ∀ k ∈ I, d k ∣ N) :
    S.partialDensity Set.univ N ≤ ∑ k ∈ I, (1 : ℝ) / (d k : ℝ) := by
  classical
  let piece (k : ℕ) := (Finset.range (N / d k)).image (fun t => d k * t)
  let A := (Finset.range N).filter (fun x => x ∈ S)
  have hsub : A ⊆ I.biUnion piece := by
    intro x hx
    obtain ⟨hr,hs⟩ := Finset.mem_filter.mp hx
    have hlt := Finset.mem_range.mp hr
    obtain ⟨k,hk,t,ht⟩ := cover x hs
    refine Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨t,Finset.mem_range.mpr ?_,ht.symm⟩⟩
    by_contra! hlarge
    have hmul : d k * (N / d k) ≤ d k * t := Nat.mul_le_mul_left _ hlarge
    have hcancel : d k * (N / d k) = N := by
      rw [Nat.mul_comm, Nat.div_mul_cancel (common k hk)]
    rw [hcancel, ← ht] at hmul
    omega
  have hcount : A.card ≤ ∑ k ∈ I, N / d k := by
    calc
      _ ≤ (I.biUnion piece).card := Finset.card_le_card hsub
      _ ≤ ∑ k ∈ I, (piece k).card := Finset.card_biUnion_le
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [piece,Finset.card_range] using
          (Finset.card_image_le (s := Finset.range (N / d k)) (f := fun t => d k * t))
  have hset : S ∩ Set.Iio N = (↑A : Set ℕ) := by
    ext x
    simp [A,and_comm]
  have hpartial : S.partialDensity Set.univ N = (A.card : ℝ) / (N : ℝ) := by
    simp [Set.partialDensity,hset]
  rw [hpartial]
  apply (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mpr
  calc
    _ ≤ ∑ k ∈ I, ((N / d k : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = ∑ k ∈ I, ((1 : ℝ) / (d k : ℝ)) * N := by
      apply Finset.sum_congr rfl
      intro k hk
      have hquot : ((N / d k : ℕ) : ℝ) = (N : ℝ) / (d k : ℝ) := by
        apply (eq_div_iff (show (d k : ℝ) ≠ 0 by exact_mod_cast (hd k hk).ne')).mpr
        exact_mod_cast Nat.div_mul_cancel (common k hk)
      rw [hquot]
      ring
    _ = _ := by rw [Finset.sum_mul]

theorem density_le_reciprocal_sum {S : Set ℕ} {δ : ℝ} (I : Finset ℕ) (d : ℕ → ℕ)
    (hd : ∀ k ∈ I, 0 < d k) (cover : ∀ x ∈ S, ∃ k ∈ I, d k ∣ x)
    (hδ : S.HasDensity δ) :
    δ ≤ ∑ k ∈ I, (1 : ℝ) / (d k : ℝ) := by
  classical
  let T := ∏ k ∈ I, d k
  have hT : 0 < T := Finset.prod_pos hd
  let block (j : ℕ) := (j+1)*T
  have grow : Tendsto block atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    calc
      b ≤ j := hj
      _ ≤ j+1 := Nat.le_succ _
      _ = (j+1)*1 := by simp
      _ ≤ block j := Nat.mul_le_mul_left _ hT
  change Tendsto (fun n : ℕ => S.partialDensity Set.univ n) atTop (𝓝 δ) at hδ
  have lim : Tendsto (fun j => S.partialDensity Set.univ (block j)) atTop (𝓝 δ) := hδ.comp grow
  apply le_of_tendsto' lim
  intro j
  apply partial_density_common_multiple I d hd cover (Nat.mul_pos (Nat.succ_pos _) hT)
  intro k hk
  have hdiv : d k ∣ T := Finset.dvd_prod_of_mem d hk
  exact dvd_mul_of_dvd_right hdiv (j+1)

theorem density_le_arithmetic_divisor_sum {S : Set ℕ} {δ : ℝ} (m K : ℕ)
    (hsub : S ⊆ {n : ℕ | ∃ k ∈ Finset.Icc 1 K, (1+k*m) ∣ n})
    (hδ : S.HasDensity δ) :
    δ ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / ((1+k*m : ℕ) : ℝ) := by
  exact density_le_reciprocal_sum (Finset.Icc 1 K) (fun k => 1+k*m)
    (fun k hk => by omega) (fun x hx => hsub hx) hδ

end Erdos697Bound

open scoped BigOperators

namespace Erdos697Delta

/-- A reciprocal sum along the progression starting at one. -/
theorem progression_sum_lt {m K : ℕ} {A : ℝ} (hm : 0 < m) (hA : 0 < A)
    (hK : (K : ℝ) < Real.exp A) :
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (1 + (k : ℝ) * m)) < (A + 1) / m := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  by_cases hk : K = 0
  · subst K
    rw [show Finset.Icc (1 : ℕ) 0 = ∅ by decide, Finset.sum_empty]
    exact div_pos (by linarith) hm'
  have hk' : 0 < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hlog : Real.log (K : ℝ) < A := (Real.log_lt_iff_lt_exp hk').mpr hK
  calc
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (1 + (k : ℝ) * m)) ≤
        ∑ k ∈ Finset.Icc 1 K, ((k : ℝ)⁻¹ / m) := by
      apply Finset.sum_le_sum
      intro k hmem
      have hkn : 0 < k := (Finset.mem_Icc.mp hmem).1
      have hkr : 0 < (k : ℝ) := by exact_mod_cast hkn
      rw [← one_div (k : ℝ), div_div]
      exact one_div_le_one_div_of_le (mul_pos hkr hm') (by linarith)
    _ = (harmonic K : ℝ) / m := by
      rw [← Finset.sum_div, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (1 + Real.log (K : ℝ)) / m :=
      div_le_div_of_nonneg_right (harmonic_le_one_add_log K) hm'.le
    _ < (A + 1) / m := (div_lt_div_iff_of_pos_right hm').mpr (by linarith)

end Erdos697Delta

open Set

namespace Erdos697Delta

theorem strict_density (m : ℕ) (α : ℝ) (hm : 0 < m) :
    Erdos697.δ m α < ((m : ℝ)^α + 1)/m := by
  classical
  let A : ℝ := (m : ℝ)^α
  let B : ℝ := Real.exp A
  let t := ⌊B⌋₊
  let K := t-1
  let S : Set ℕ := {n : ℕ | ∃ d : ℕ, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Ioo 1 B ∧ d ∣ n}
  have hA : 0 < A := Real.rpow_pos_of_pos (by exact_mod_cast hm) _
  have hB : 1 < B := Real.one_lt_exp_iff.mpr hA
  have hfloor : (t : ℝ) ≤ B := Nat.floor_le (by linarith)
  have ht : 1 ≤ t := Nat.le_floor (by simpa using hB.le)
  have hKt : K+1=t := by dsimp only [K]; omega
  have hKtr : (K : ℝ)+1=(t : ℝ) := by exact_mod_cast hKt
  have hK : (K : ℝ) < Real.exp A := by change (K : ℝ) < B; linarith
  have hsubset : S ⊆ {n : ℕ | ∃ k ∈ Finset.Icc 1 K, 1+k*m ∣ n} := by
    rintro n ⟨d, hmod, hd, hdn⟩
    have hd1 : 1 < d := by exact_mod_cast hd.1
    have hdt : d ≤ t := Nat.le_floor hd.2.le
    obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' (by omega : 1 ≤ d)).mp hmod.symm
    have he : d=1+k*m := by rw [Nat.mul_comm] at hk; omega
    have hkp : 0 < k := by by_contra! h; simp [show k=0 by omega] at he; omega
    have hkm : k ≤ k*m := by simpa using (Nat.mul_le_mul_left k hm)
    refine ⟨k, Finset.mem_Icc.mpr ⟨hkp, by omega⟩, ?_⟩
    rwa [← he]
  have hs : S.HasDensity (Erdos697.δ m α) := (existsDensityChecked m α).choose_spec
  have hsum := Erdos697Bound.density_le_arithmetic_divisor_sum m K hsubset hs
  push_cast at hsum
  exact lt_of_le_of_lt hsum (progression_sum_lt hm hA hK)

end Erdos697Delta

theorem OMA.solution : type_of% @Erdos697.erdos_697.variants.delta_lt :=
  Erdos697Delta.strict_density

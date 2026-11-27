import FormalConjectures.OEIS.«215926»
import Mathlib

/-!
# Range of the least deficient multiplier

The proof that every sequence value is either three or almost perfect is
adapted from @Hiphex's accepted A215926 reduction (open-math-agents #4232),
which credits Naitik Gupta's earlier first-occurrence argument (#906).
The attainment direction uses Mathlib's finite lower bound for sums of
prime reciprocals to construct a product of distinct large primes.
-/

namespace OMA.AlmostPerfectConverse

open OeisA215926
open scoped ArithmeticFunction.sigma

private theorem nondeficient_iff {n : ℕ} (hn : 0 < n) :
    n.Perfect ∨ n.Abundant ↔ 2 * n ≤ σ 1 n := by
  rw [ArithmeticFunction.sigma_one_apply,
    Nat.perfect_iff_sum_divisors_eq_two_mul hn, Nat.abundant_iff_sum_divisors]
  omega

private theorem nondeficient_mul_of_dvd {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (h : r ∣ n) (hs : r.Perfect ∨ r.Abundant) : n.Perfect ∨ n.Abundant := by
  have abundancy {t : ℕ} (ht : 0 < t) : t.Perfect ∨ t.Abundant ↔ 2 ≤ t.abundancyIndex := by
    rw [nondeficient_iff ht, ArithmeticFunction.sigma_one_apply, Nat.abundancyIndex,
      le_div_iff₀ (by positivity)]
    norm_cast
  exact (abundancy hn).mpr ((abundancy hr).mp hs |>.trans
    (Nat.abundancyIndex_le_of_dvd hn.ne' h))

private theorem sigma_two_pow (j : ℕ) : σ 1 (2 ^ j) + 1 = 2 * 2 ^ j := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    Nat.geomSum_eq (m := 2) (by decide), pow_succ]
  have := Nat.two_pow_pos j
  omega

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = 1 + p := by
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors]
  simp [Ne.symm hp.ne_one]

private theorem pow_mul_prime_nondeficient {j p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p < 2 * 2 ^ j) : ((2 ^ j) * p).Perfect ∨ ((2 ^ j) * p).Abundant := by
  apply (nondeficient_iff (Nat.mul_pos (Nat.two_pow_pos _) hp.pos)).mpr
  have hcop : (2 ^ j).Coprime p := (hp.odd_of_ne_two hp2).coprime_two_left.pow_left j
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp]
  have hσ := sigma_two_pow j
  have hd : p ≤ σ 1 (2 ^ j) := by omega
  nlinarith only [hd, congrArg (· * p) hσ]

private theorem replace_by_power {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hkn : k.Coprime n) (hodd : Odd n) (hdeficit : σ 1 k + 2 ≤ 2 * k)
    (hnondef : (k * n).Perfect ∨ (k * n).Abundant) :
    ((2 ^ (Nat.log 2 k)) * n).Perfect ∨ ((2 ^ (Nat.log 2 k)) * n).Abundant := by
  let j := Nat.log 2 k
  let x := 2 ^ j
  change (x * n).Perfect ∨ (x * n).Abundant
  have hx : 0 < x := by dsimp [x]; positivity
  have hkx : k ≤ 2 * x := by
    have hlog := Nat.lt_pow_succ_log_self Nat.one_lt_two k
    rw [Nat.succ_eq_add_one, pow_succ] at hlog
    dsimp [x, j]
    omega
  have hσ : σ 1 x + 1 = 2 * x := sigma_two_pow j
  have hcompare : σ 1 k * x ≤ σ 1 x * k := by
    have h₁ := Nat.mul_le_mul_right x hdeficit
    have h₂ := congrArg (· * k) hσ
    nlinarith only [h₁, h₂, hkx]
  have hnorm := (nondeficient_iff (Nat.mul_pos hk hn)).mp hnondef
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hkn] at hnorm
  have hxcop : x.Coprime n := hodd.coprime_two_left.pow_left j
  apply (nondeficient_iff (Nat.mul_pos hx hn)).mpr
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hxcop]
  have h₁ := Nat.mul_le_mul_right x hnorm
  have h₂ := Nat.mul_le_mul_right (σ 1 n) hcompare
  apply Nat.le_of_mul_le_mul_right (c := k) _ hk
  calc
    (2 * (x * n)) * k = (2 * (k * n)) * x := by ring
    _ ≤ (σ 1 k * σ 1 n) * x := h₁
    _ = (σ 1 k * x) * σ 1 n := by ring
    _ ≤ (σ 1 x * k) * σ 1 n := h₂
    _ = (σ 1 x * σ 1 n) * k := by ring

/-- Every least deficient multiplier other than three is almost perfect. -/
theorem three_or_almost (n : ℕ) (hn : 2 ≤ n) :
    OeisA215926.a n = 3 ∨ 1 + σ 1 (OeisA215926.a n) = 2 * OeisA215926.a n := by
  let S := {k : ℕ | k.Deficient ∧ ((k * n).Perfect ∨ (k * n).Abundant)}
  have hnp : 0 < n := by omega
  change sInf S = 3 ∨ 1 + σ 1 (sInf S) = 2 * sInf S
  by_cases hn₂ : 2 ∣ n
  · have hs : 3 ∈ S :=
      ⟨Nat.deficient_three, nondeficient_mul_of_dvd (by decide) (Nat.mul_pos (by decide) hnp)
        (Nat.mul_dvd_mul_left 3 hn₂) (Or.inl (by constructor <;> decide))⟩
    have hmin := Nat.sInf_mem (show S.Nonempty from ⟨3, hs⟩)
    have hp : 0 < sInf S := hmin.1.pos
    have hmax : sInf S ≤ 3 := Nat.sInf_le hs
    interval_cases h : sInf S <;> first
      | exact Or.inl rfl
      | exact Or.inr (by simpa only [pow_zero, Nat.add_comm] using sigma_two_pow 0)
      | exact Or.inr (by simpa only [pow_one, Nat.add_comm] using sigma_two_pow 1)
  · have hodd : Odd n := Nat.not_even_iff_odd.mp (fun h => hn₂ (even_iff_two_dvd.mp h))
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ n := Nat.minFac_dvd n
    have hp₂ : p ≠ 2 := fun he => hn₂ (he ▸ hpd)
    let j := Nat.log 2 p
    let x := 2 ^ j
    have hx : x < p := by
      have hxle : x ≤ p := Nat.pow_log_le_self 2 hp.ne_zero
      refine lt_of_le_of_ne hxle ?_
      intro he
      have hd : p ∣ 2 ^ j := he.symm ▸ dvd_rfl
      exact hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    have hpx : p < 2 * x := by
      have h := Nat.lt_pow_succ_log_self Nat.one_lt_two p
      simpa [x, j, pow_succ, Nat.mul_comm] using h
    have hxp : 0 < x := Nat.two_pow_pos j
    have hs : x ∈ S :=
      ⟨Nat.prime_two.deficient_pow,
        nondeficient_mul_of_dvd (Nat.mul_pos hxp hp.pos) (Nat.mul_pos hxp hnp)
          (Nat.mul_dvd_mul_left x hpd) (pow_mul_prime_nondeficient hp hp₂ hpx)⟩
    let k := sInf S
    have hk : k ∈ S := Nat.sInf_mem ⟨x, hs⟩
    have hkp : k < p := (Nat.sInf_le hs).trans_lt hx
    by_cases hσ : 1 + σ 1 k = 2 * k
    · exact Or.inr hσ
    · have hd := hk.1
      have hσ' : σ 1 k < 2 * k := by
        rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
        unfold Nat.Deficient at hd
        omega
      have hdeficit : σ 1 k + 2 ≤ 2 * k := by
        omega
      have hpow : 2 ^ (Nat.log 2 k) ∈ S :=
        ⟨Nat.prime_two.deficient_pow,
          replace_by_power hd.pos hnp (Nat.coprime_of_lt_minFac hd.pos.ne' hkp).symm
            hodd hdeficit hk.2⟩
      have he : k = 2^(Nat.log 2 k) :=
        (Nat.sInf_le hpow).antisymm (Nat.pow_log_le_self 2 hd.pos.ne')
      change k=3 ∨ 1+σ 1 k=2*k
      exact Or.inr (by simpa only [← he, Nat.add_comm] using sigma_two_pow (Nat.log 2 k))

end OMA.AlmostPerfectConverse

namespace OMA.AlmostPerfectConverse

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem sum_le_expansion (s : Finset ℕ) :
    1 + ∑ p ∈ s, (1 / p : ℝ) ≤ ∏ p ∈ s, (1 + 1 / p : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [sum_insert hp, prod_insert hp]
    have hsum : 0 ≤ ∑ r ∈ s, (1 / r : ℝ) := sum_nonneg (fun _ _ => by positivity)
    have hmul := mul_le_mul_of_nonneg_left ih (show (0:ℝ) ≤ 1+1/p by positivity)
    nlinarith only [hmul, mul_nonneg (show (0:ℝ) ≤ 1/p by positivity) hsum]

private theorem find_subproduct {s : Finset ℕ} {a b : ℝ} (ha : 1 < a)
    (steps : ∀ p ∈ s, a*(1+1/p) < b)
    (endpt : a ≤ ∏ p ∈ s, (1+1/p : ℝ)) :
    ∃ t ⊆ s, a ≤ (∏ p ∈ t, (1+1/p : ℝ)) ∧ (∏ p ∈ t, (1+1/p : ℝ)) < b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty] at endpt
    exact False.elim (ha.not_ge endpt)
  | @insert p s hp ih =>
    by_cases hs : a ≤ ∏ r ∈ s, (1+1/r : ℝ)
    · obtain ⟨t,ht,hl,hu⟩ := ih (fun r hr => steps r (mem_insert_of_mem hr)) hs
      exact ⟨t, fun _ h => mem_insert_of_mem (ht h), hl, hu⟩
    · refine ⟨insert p s, Subset.rfl, endpt, ?_⟩
      rw [prod_insert hp, mul_comm]
      exact (mul_lt_mul_of_pos_right (lt_of_not_ge hs)
        (show (0:ℝ) < 1+1/p by positivity)).trans (steps p (mem_insert_self p s))

private theorem prime_product_data (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    let n := ∏ p ∈ s, p
    0 < n ∧ (∀ q : ℕ, q.Prime → q ∣ n → q ∈ s) ∧
      (σ 1 n : ℝ) / n = ∏ p ∈ s, (1+1/p : ℝ) := by
  classical
  dsimp only
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, Nat.cast_one, div_one]
    refine ⟨by decide, ?_, by simp⟩
    intro p hp hd
    exact (hp.not_dvd_one hd).elim
  | @insert p s hps ih =>
    have hP := hs p (mem_insert_self p s)
    obtain ⟨hn,hf,hA⟩ := ih (fun q hq => hs q (mem_insert_of_mem hq))
    rw [prod_insert hps, prod_insert hps]
    have hc : p.Coprime (∏ r ∈ s, r) := hP.coprime_iff_not_dvd.mpr (fun h => hps (hf p hP h))
    have hsig : σ 1 p = 1 + p := by
      rw [sigma_one_apply, hP.divisors]
      simp [Ne.symm hP.ne_one]
    refine ⟨mul_pos hP.pos hn, ?_, ?_⟩
    · intro q hq hd
      rcases hq.dvd_mul.mp hd with h | h
      · exact mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hP).mp h))
      · exact mem_insert_of_mem (hf q hq h)
    · rw [isMultiplicative_sigma.map_mul_of_coprime hc, hsig, Nat.cast_mul,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, ← hA, mul_div_mul_comm]
      have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hP.ne_zero
      have hratio : ((1:ℝ)+p)/p = 1+1/p := by field_simp; ring
      rw [hratio]

/-- A squarefree product of primes larger than any given bound can attain
any abundancy interval with lower endpoint between one and three halves. -/
theorem exists_rough_abundancy (K : ℕ) {a b : ℝ} (ha : 1<a)
    (hab : a<b) (hhalf : a≤3/2) :
    ∃ n : ℕ, 1<n ∧ K<n.minFac ∧ a ≤ (σ 1 n : ℝ)/n ∧ (σ 1 n : ℝ)/n < b := by
  classical
  obtain ⟨L,hL⟩ := exists_nat_gt (max (K:ℝ) (a/(b-a)))
  have hKL : (K:ℝ) < L := (le_max_left ..).trans_lt hL
  have hlevel : a/(b-a) < L := (le_max_right ..).trans_lt hL
  let s := (4^(L.primesBelow.card+1)).succ.primesBelow \ L.primesBelow
  have data (p : ℕ) (hp : p ∈ s) : p.Prime ∧ L ≤ p := by
    obtain ⟨hin,hout⟩ := mem_sdiff.mp hp
    have hP := Nat.prime_of_mem_primesBelow hin
    exact ⟨hP, by simpa [Nat.primesBelow, hP] using hout⟩
  have hbig : a ≤ ∏ p ∈ s, (1+1/p : ℝ) := by
    have hs : (1/2:ℝ) ≤ ∑ p ∈ s, (1/p : ℝ) := one_half_le_sum_primes_ge_one_div L
    linarith only [hs, hhalf, sum_le_expansion s]
  have steps (p : ℕ) (hp : p ∈ s) : a*(1+1/p) < b := by
    have hpR : (0:ℝ)<p := by exact_mod_cast (data p hp).1.pos
    have hLp : (L:ℝ)≤p := by exact_mod_cast (data p hp).2
    have h := (div_lt_iff₀ (sub_pos.mpr hab)).mp (hlevel.trans_le hLp)
    have hdiv : a/p < b-a := (div_lt_iff₀ hpR).mpr (by nlinarith only [h])
    calc
      a*(1+1/p) = a+a/p := by ring
      _ < b := by linarith only [hdiv]
  obtain ⟨t,ht,hl,hu⟩ := find_subproduct ha steps hbig
  let n := ∏ p ∈ t, p
  obtain ⟨hn,hpr,hA⟩ := prime_product_data t (fun p h => (data p (ht h)).1)
  change (σ 1 n : ℝ)/n = _ at hA
  have hn1 : n ≠ 1 := by
    intro he
    rw [← hA, he] at hl
    simp at hl
    linarith
  have hmin := hpr n.minFac (Nat.minFac_prime hn1) (Nat.minFac_dvd n)
  have hKL' : K<L := by exact_mod_cast hKL
  exact ⟨n, by change 0 < n at hn; omega, hKL'.trans_le (data _ (ht hmin)).2,
    by simpa only [hA] using hl, by simpa only [hA] using hu⟩

end OMA.AlmostPerfectConverse

namespace OMA.AlmostPerfectConverse

open Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem nondeficient_test {m : ℕ} (hm : 0<m) :
    m.Perfect ∨ m.Abundant ↔ 2*m ≤ σ 1 m := by
  rw [sigma_one_apply, Nat.perfect_iff_sum_divisors_eq_two_mul hm,
    Nat.abundant_iff_sum_divisors]
  omega

/-- Every almost-perfect natural number is attained, with every prime
dividing the witnessing argument larger than the desired multiplier. -/
theorem almost_perfect_is_attained {k : ℕ} (hk : 2≤k) (hit : 1 + σ 1 k = 2*k) :
    ∃ n ≥ 2, k<n.minFac ∧ OeisA215926.a n=k := by
  have hk0 : 0<k := by omega
  have hKR : (2:ℝ)≤k := by exact_mod_cast hk
  let x : ℝ := (k:ℝ)-1
  have hx : 1≤x := by dsimp [x]; linarith
  have hXK : x<k := by dsimp [x]; linarith
  have dx : 0 < 2*x-1 := by linarith
  have dk : 0 < 2*(k:ℝ)-1 := by linarith
  have ha : 1 < 2*(k:ℝ)/(2*k-1) := (lt_div_iff₀ dk).mpr (by linarith)
  have hab : 2*(k:ℝ)/(2*k-1) < 2*x/(2*x-1) :=
    (div_lt_div_iff₀ dk dx).mpr (by nlinarith only [hXK])
  have hhalf : 2*(k:ℝ)/(2*k-1) ≤ 3/2 :=
    (div_le_iff₀ dk).mpr (by linarith only [hKR])
  obtain ⟨n,hn,hrough,hlo,hhi⟩ := exists_rough_abundancy k ha hab hhalf
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have low := (div_le_div_iff₀ dk hnR).mp hlo
  have high := (div_lt_div_iff₀ hnR dx).mp hhi
  have hsig : (σ 1 k : ℝ) = 2*k-1 := by
    have h : (1:ℝ)+(σ 1 k:ℝ) = 2*k := by exact_mod_cast hit
    linarith
  have mult {m : ℕ} (hm : 0<m) (hmk : m≤k) :
      σ 1 (m*n) = σ 1 m * σ 1 n :=
    isMultiplicative_sigma.map_mul_of_coprime
      (Nat.coprime_of_lt_minFac hm.ne' (hmk.trans_lt hrough)).symm
  let S := {m : ℕ | m.Deficient ∧ ((m*n).Perfect ∨ (m*n).Abundant)}
  have hmem : k ∈ S := by
    constructor
    · have hsum := hit
      rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at hsum
      unfold Nat.Deficient
      omega
    · apply (nondeficient_test (Nat.mul_pos hk0 hn0)).mpr
      rw [mult hk0 le_rfl]
      have h : 2*((k:ℝ)*n) ≤ (σ 1 k : ℝ)*(σ 1 n:ℝ) := by
        rw [hsig]
        nlinarith only [low]
      exact_mod_cast h
  have lower (m : ℕ) (hmem' : m ∈ S) : k ≤ m := by
    by_contra! hmk
    have hd := hmem'.1
    have hm := hd.pos
    have hbound : σ 1 m + 1 ≤ 2*m := by
      rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
      unfold Nat.Deficient at hd
      omega
    have hboundR : (σ 1 m : ℝ) + 1 ≤ 2*m := by exact_mod_cast hbound
    have hmkR : (m:ℝ)+1 ≤ k := by exact_mod_cast (show m+1 ≤ k by omega)
    have hmx : (m:ℝ) ≤ x := by dsimp [x]; linarith only [hmkR]
    have hx0 : 0≤x := by linarith
    have hsmall : (σ 1 m : ℝ)*x ≤ (2*x-1)*(m:ℝ) := by
      nlinarith only [mul_le_mul_of_nonneg_right hboundR hx0, hmx]
    have h2 := (nondeficient_test (Nat.mul_pos hm hn0)).mp hmem'.2
    rw [mult hm hmk.le] at h2
    have h2R : 2*((m:ℝ)*n) ≤ (σ 1 m:ℝ)*(σ 1 n:ℝ) := by exact_mod_cast h2
    have hmR : (0:ℝ)<m := by exact_mod_cast hm
    have h1 := mul_le_mul_of_nonneg_right hsmall (show (0:ℝ)≤σ 1 n by positivity)
    have h3 := mul_lt_mul_of_pos_right high hmR
    have h4 := mul_le_mul_of_nonneg_right h2R hx0
    nlinarith only [h1,h3,h4]
  exact ⟨n, by omega, hrough, (Nat.sInf_le hmem).antisymm
    (lower _ (Nat.sInf_mem ⟨k,hmem⟩))⟩

end OMA.AlmostPerfectConverse

namespace OMA.AlmostPerfectConverse

open Nat
open scoped ArithmeticFunction.sigma

/-- The range of the least-deficient-multiplier sequence on its domain
is exactly three together with all the almost-perfect natural numbers. -/
theorem range_characterization (k : ℕ) :
    (∃ n ≥ 2, OeisA215926.a n=k) ↔ k=3 ∨ 1+σ 1 k=2*k := by
  constructor
  · rintro ⟨n,hn,rfl⟩
    exact three_or_almost n hn
  · rintro (rfl | hit)
    · exact ⟨2, by decide, OeisA215926.a_2⟩
    · by_cases hk : 2≤k
      · obtain ⟨n,hn,_,e⟩ := almost_perfect_is_attained hk hit
        exact ⟨n,hn,e⟩
      · have hk1 : k=1 := by
          by_cases h0 : k=0
          · simp [h0] at hit
          · omega
        exact ⟨6, by decide, by simpa [hk1] using OeisA215926.a_6⟩

/-- The OEIS conjecture holds precisely when every almost-perfect number
is a power of two. -/
theorem conjecture_iff_only_powers :
    (type_of% @OeisA215926.conjecture_1) ↔
      ∀ k : ℕ, 1 + σ 1 k = 2*k → k.isPowerOfTwo := by
  have hthree : σ 1 3=4 := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.prime_three.divisors]
    decide
  constructor
  · intro law k hit
    obtain ⟨n,hn,he⟩ := (range_characterization k).mpr (Or.inr hit)
    obtain (h | h | h) := law n hn
    · exact ⟨0, he.symm.trans h⟩
    · have hk : k=3 := he.symm.trans h
      rw [hk,hthree] at hit
      omega
    · exact he ▸ h
  · intro h n hn
    rcases (range_characterization (OeisA215926.a n)).mp ⟨n,hn,rfl⟩ with h3 | halmost
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (h _ halmost))

end OMA.AlmostPerfectConverse

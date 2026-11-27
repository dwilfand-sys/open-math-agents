import OMAStatements.S_oeis_a085265
import Mathlib

/-!
# A positive square plus a positive squarefree number

Source: https://oeis.org/A085265
Credit: @dwilfand-sys (proof prepared by Codex). Statement by @niclorusso.

For large inputs, select square roots of a suitable parity and remove common
factors with the product of the odd primes whose squares divide the input.
Ordinary prime-square obstructions occupy two residue classes. We count these
by inclusion–exclusion and use the elementary estimate `primorial_le_four_pow`
in the large range. Intermediate interval bounds use Legendre's finite sieve.
The initial segment is certified by taking unions and intersections of bit masks.

This proof is independent of the nonnegative-square representation theorem in
J. Jiménez Urroz, *Every integer can be written as a square plus a squarefree*,
Expositiones Mathematicae 40 (2022), 665–678, DOI 10.1016/j.exmath.2021.12.002.
Dudek and Platt proved that every integer n ≥ 10 outside 1 modulo 4 is a
prime square plus a squarefree integer, DOI 10.1112/S1461157015000297.
The present direct sieve includes the residue class 1 modulo 4.
-/

open scoped BigOperators

namespace A085265Sieve

private def primeWeight (p : ℕ) : ℕ := if 2 < p ∧ p.Prime then 1 else 0

private def wheelWeight (n : ℕ) : ℕ :=
  if n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 then 1 else 0

private lemma count_eq_sum (n : ℕ) :
    ((Finset.range n).filter fun p => 2 < p ∧ p.Prime).card =
      ∑ p ∈ Finset.range n, primeWeight p := by
  simpa only [primeWeight, Nat.cast_id] using
    (Finset.sum_boole (R := ℕ) (fun p : ℕ => 2 < p ∧ p.Prime) (Finset.range n)).symm

private lemma prime_block (n : ℕ) (hn : 5 < n) :
    ((Finset.range (n + 30)).filter fun p => 2 < p ∧ p.Prime).card ≤
      ((Finset.range n).filter fun p => 2 < p ∧ p.Prime).card + 8 := by
  have count : ∀ r : Fin 30, (∑ i ∈ Finset.range 30, wheelWeight (r.val+i)) = 8 := by
    decide +kernel
  have hsum : (∑ i ∈ Finset.range 30, primeWeight (n+i)) ≤
      ∑ i ∈ Finset.range 30, wheelWeight (n%30+i) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : 2 < n+i ∧ (n+i).Prime
    · have hnd {d : ℕ} (hd : d.Prime) (hlt : d < n+i) : ¬ d ∣ n+i := by
        intro hdvd
        exact (ne_of_lt hlt) ((Nat.prime_dvd_prime_iff_eq hd h.2).mp hdvd)
      have h2 := hnd Nat.prime_two (by omega)
      have h3 := hnd Nat.prime_three (by omega)
      have h5 := hnd (d := 5) (by decide) (by omega)
      have hr : (n%30+i)%2 ≠ 0 ∧ (n%30+i)%3 ≠ 0 ∧ (n%30+i)%5 ≠ 0 := by omega
      simp [primeWeight, wheelWeight, h, hr]
    · simp [primeWeight, h]
  have h8 := count ⟨n%30, Nat.mod_lt _ (by decide)⟩
  change (∑ i ∈ Finset.range 30, wheelWeight (n%30+i)) = 8 at h8
  rw [count_eq_sum, count_eq_sum, Finset.sum_range_add]
  exact Nat.add_le_add_left (hsum.trans_eq h8) _

theorem primeCountWheel (J : ℕ) (hJ : 10 ≤ J) :
    15 * ((Finset.range (2*J+2)).filter (fun p => 2 < p ∧ Nat.Prime p)).card ≤ 8*J+34 := by
  induction J using Nat.strong_induction_on with
  | ind J ih =>
    by_cases hs : J < 25
    · have base : ∀ j : Fin 25, 10 ≤ j.val →
          15 * ((Finset.range (2*j.val+2)).filter
            (fun p => 2 < p ∧ Nat.Prime p)).card ≤ 8*j.val+34 := by decide +kernel
      exact base ⟨J,hs⟩ hJ
    · let k := J - 15
      have hk : 10 ≤ k := by dsimp [k]; omega
      have hkJ : k < J := by dsimp [k]; omega
      have hJk : J = k + 15 := by dsimp [k]; omega
      have head := ih k hkJ hk
      have tail := prime_block (2*k+2) (by omega)
      rw [show 2*J+2 = (2*k+2)+30 by omega]
      omega

end A085265Sieve

namespace A085265Sieve

/-! A bit at index `n` records a possible failure. The sieve and the fourteen
translations are computations on natural-number literals in the Lean kernel. -/

private def lowBits (width : ℕ) : ℕ := ((1 : ℕ) <<< width) - 1

private theorem lowBits_at (width n : ℕ) :
    (lowBits width).testBit n = decide (n < width) := by
  simpa only [lowBits, Nat.shiftLeft_eq, one_mul] using
    Nat.testBit_two_pow_sub_one width n

/-- One periodic row. Doubling the stride separates the even and odd indices
of its multiples. Stop once the next stride would leave the interval. -/
private def multiplesRow : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, d =>
    if 365000 < d then 1 else
      let row := multiplesRow fuel (2*d)
      row ||| (row <<< d)

private theorem multiplesRow_marks (fuel d k : ℕ) (hd : 0 < d)
    (hk : k < 2^fuel) (hbound : d*k ≤ 365000) :
    (multiplesRow fuel d).testBit (d*k) = true := by
  induction fuel generalizing d k with
  | zero =>
    have hk0 : k = 0 := by
      rw [pow_zero] at hk
      omega
    simp [multiplesRow, hk0]
  | succ fuel ih =>
    by_cases hstop : 365000 < d
    · have hk0 : k = 0 := by
        by_contra hne
        have hle : d ≤ d*k := by
          simpa using Nat.mul_le_mul_left d (show 1 ≤ k by omega)
        omega
      simp [multiplesRow, hstop, hk0]
    · have hquot : k/2 < 2^fuel := by
        rw [pow_succ] at hk
        omega
      have hreorder : (2*d)*(k/2) = d*(2*(k/2)) := by ring
      have hle : (2*d)*(k/2) ≤ d*k := by
        rw [hreorder]
        exact Nat.mul_le_mul_left _ (by omega)
      have hrec := ih (2*d) (k/2) (by omega) hquot (hle.trans hbound)
      rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
      · have hki : 2*(k/2) = k := by omega
        have hindex : d*k = (2*d)*(k/2) := by rw [hreorder, hki]
        simp only [multiplesRow, if_neg hstop, Nat.testBit_or, hindex, hrec, Bool.true_or]
      · have hki : 2*(k/2)+1 = k := by omega
        have hindex : (2*d)*(k/2)+d = d*k := by
          calc
            _ = d*(2*(k/2)+1) := by ring
            _ = _ := by rw [hki]
        have hsub : d*k-d = (2*d)*(k/2) := by omega
        have hge : d ≤ d*k := by omega
        simp [multiplesRow, hstop, Nat.testBit_or, Nat.testBit_shiftLeft,
          hge, hsub, hrec]

/-- Rows for every possible square divisor `d²`, where `2 ≤ d ≤ count+1`. -/
private def squareDivisorMask : ℕ → ℕ
  | 0 => 1
  | count+1 => squareDivisorMask count ||| multiplesRow 19 ((count+2)^2)

private theorem squareDivisorMask_marks (count d k : ℕ)
    (hd : 2 ≤ d) (hcount : d ≤ count+1) (hbound : d^2*k ≤ 365000) :
    (squareDivisorMask count).testBit (d^2*k) = true := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [squareDivisorMask, Nat.testBit_or]
    by_cases h : d = count+2
    · subst d
      have hpos : 0 < (count+2)^2 := by positivity
      have hmult : k ≤ (count+2)^2*k := by
        simpa using Nat.mul_le_mul_right k (show 1 ≤ (count+2)^2 by omega)
      have hsize : k < 2^19 := by norm_num; omega
      rw [multiplesRow_marks 19 _ k hpos hsize hbound, Bool.or_true]
    · rw [ih (by omega), Bool.true_or]

private theorem nonsquarefree_marked {n : ℕ} (hn : 0 < n)
    (hmax : n ≤ 365000) (hbad : ¬ Squarefree n) :
    (squareDivisorMask 603).testBit n = true := by
  rw [Nat.squarefree_iff_prime_squarefree] at hbad
  push_neg at hbad
  obtain ⟨p, hp, hdiv⟩ := hbad
  have hd : p^2 ∣ n := by simpa only [pow_two] using hdiv
  have hsq := Nat.le_of_dvd hn hd
  have hmaxp : p ≤ 604 := by
    by_contra! h
    have h605 : 605^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
    norm_num at h605
    omega
  obtain ⟨k, rfl⟩ := hd
  exact squareDivisorMask_marks 603 p k hp.two_le hmaxp hmax

/-- Intersect the masks for the first `k` positive squares. The low bits in
each translation account for the requirement that the remainder be positive. -/
private def failureMask : ℕ → ℕ → ℕ
  | 0, _ => lowBits 365001
  | k+1, mask => failureMask k mask &&&
      ((mask <<< ((k+1)^2)) ||| lowBits ((k+1)^2+1))

private theorem failureMask_marks (k n : ℕ) (hmax : n ≤ 365000)
    (hfail : ∀ w : ℕ, 0 < w → w ≤ k → w^2 < n → ¬ Squarefree (n-w^2)) :
    (failureMask k (squareDivisorMask 603)).testBit n = true := by
  induction k with
  | zero =>
    rw [failureMask, lowBits_at, decide_eq_true_eq]
    omega
  | succ k ih =>
    have hold := ih (fun w hw hle hlt => hfail w hw (by omega) hlt)
    rw [failureMask, Nat.testBit_and, hold, Bool.true_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, lowBits_at]
    by_cases hfit : (k+1)^2 < n
    · have hm := nonsquarefree_marked (n := n-(k+1)^2) (by omega)
          (by omega) (hfail (k+1) (by omega) le_rfl hfit)
      simp [hfit.le, hm]
    · have hlow : n < (k+1)^2+1 := by omega
      simp [hlow]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_mask_certificate : failureMask 14 (squareDivisorMask 603) = 8195 := by
  decide +kernel

private theorem finite_mask_exceptions (n : ℕ) (h : (8195 : ℕ).testBit n = true) :
    n = 0 ∨ n = 1 ∨ n = 13 := by
  have bits : (8195 : ℕ) = (2^0 ||| 2^1 ||| 2^13) := by decide
  rw [bits] at h
  simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at h
  omega

/-- Every positive input through 365000 other than 1 and 13 has a positive
squarefree remainder after subtracting a square with root at most 14. -/
theorem squarefree_finite {n : ℕ} (hn : 0 < n) (hN : n ≤ 365000)
    (h1 : n ≠ 1) (h13 : n ≠ 13) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 14 ∧ k^2 < n ∧ Squarefree (n-k^2) := by
  by_contra h
  have hmask := failureMask_marks 14 n hN (fun w hw hle hlt hs =>
    h ⟨w, hw, hle, hlt, hs⟩)
  rw [finite_mask_certificate] at hmask
  rcases finite_mask_exceptions n hmask with h0 | he1 | he13 <;> omega

end A085265Sieve

namespace A085265Sieve

def largePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => 2 < p ∧ Nat.Prime p)

def largePi (N : ℕ) : ℕ := (largePrimeSet N).card

def largeRho (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1-1/(p:ℚ))

private def oddFactors (S : Finset ℕ) : Prop := ∀ p ∈ S, 2 < p ∧ p.Prime

private lemma largePi_le (N : ℕ) : largePi N ≤ N := by
  have h : largePrimeSet N ⊆ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hN,hp,_⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_of_lt_succ (Finset.mem_range.mp hN)⟩
  have hc := Finset.card_le_card h
  simpa [largePi, Nat.card_Icc] using hc

/-- The primes above a power of two give a lower bound for the primorial. -/
theorem large_prime_cutoff (M s : ℕ) :
    s*largePi M ≤ 2*M + s*largePi (2^s) := by
  let U := (largePrimeSet M).filter (fun p => 2^s < p)
  have hcover : largePrimeSet M ⊆ largePrimeSet (2^s) ∪ U := by
    intro p hp
    by_cases h : 2^s < p
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), (Finset.mem_filter.mp hp).2⟩)
  have hcard : largePi M ≤ largePi (2^s) + U.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hsub : U ⊆ (Finset.range (M+1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hp,_⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,_,hprime⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hn,hprime⟩
  have hprod : (∏ p ∈ U, p) ≤ primorial M :=
    Nat.le_of_dvd (primorial_pos _) (Finset.prod_dvd_prod_of_subset U _ (fun p : ℕ => p) hsub)
  have hpow : (2:ℕ)^(s*U.card) ≤ 2^(2*M) := calc
    _ = ∏ _p ∈ U, (2:ℕ)^s := by rw [Finset.prod_const, pow_mul]
    _ ≤ ∏ p ∈ U, p := Finset.prod_le_prod' (fun p hp => le_of_lt (Finset.mem_filter.mp hp).2)
    _ ≤ primorial M := hprod
    _ ≤ 4^M := primorial_le_four_pow M
    _ = 2^(2*M) := by rw [pow_mul] <;> rfl
  have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  have hc := Nat.mul_le_mul_left s hcard
  rw [Nat.mul_add] at hc
  omega

private lemma pi_fixed : largePi 65536 ≤ 22000 := by
  have hh := primeCountWheel 32768 (by decide)
  have hsub : largePrimeSet 65536 ⊆ (Finset.range (2*32768+2)).filter
      (fun p => 2 < p ∧ Nat.Prime p) := by
    intro p hp
    obtain ⟨h,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp h; omega), hp⟩
  have hc := Finset.card_le_card hsub
  change (largePrimeSet 65536).card ≤ 22000
  omega

private def rankedPrime (skip : Bool) (k : ℕ) : ℕ :=
  ([3,5,7,11,13,17,19,23,29,31,37] : List ℕ).getD
    (k + (if skip then 1 else 0)) 1

private def rankedProd (skip : Bool) : ℕ → ℕ
  | 0 => 1
  | k+1 => rankedProd skip k * rankedPrime skip k

private def rankedRho (skip : Bool) : ℕ → ℚ
  | 0 => 1
  | k+1 => rankedRho skip k * (1-1/(rankedPrime skip k:ℚ))

private lemma ranked_table (skip : Bool) (k : ℕ) (hk : k < 10) :
    2 < rankedPrime skip k ∧
    ((Finset.range (rankedPrime skip k)).filter
      (fun p => 2 < p ∧ p.Prime ∧ (skip = true → p ≠ 3))).card = k := by
  have table : ∀ b : Bool, ∀ i : Fin 10, 2 < rankedPrime b i.val ∧
      ((Finset.range (rankedPrime b i.val)).filter
        (fun p => 2 < p ∧ p.Prime ∧ (b = true → p ≠ 3))).card = i.val := by decide +kernel
  exact table skip ⟨k,hk⟩

private lemma rho_nonneg {S : Finset ℕ} (hS : oddFactors S) : 0 ≤ largeRho S := by
  apply Finset.prod_nonneg
  intro p hp
  have ht := (hS p hp).1
  have hq : (1:ℚ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  exact sub_nonneg.mpr ((div_le_one (by linarith : 0 < (p:ℚ))).mpr hq)

private lemma ranked_bounds (skip : Bool) (k : ℕ) (hk : k ≤ 10)
    (S : Finset ℕ) (hc : S.card=k) (hS : oddFactors S) (hskip : skip = true → 3 ∉ S) :
    rankedProd skip k ≤ ∏ p ∈ S, p ∧ rankedRho skip k ≤ largeRho S := by
  induction k generalizing S with
  | zero =>
    have he : S = ∅ := Finset.card_eq_zero.mp hc
    subst S
    simp [rankedProd, rankedRho, largeRho]
  | succ k ih =>
    have tab := ranked_table skip k (by omega)
    have hp : ∃ p ∈ S, rankedPrime skip k ≤ p := by
      by_contra! h
      have sub : S ⊆ (Finset.range (rankedPrime skip k)).filter
          (fun p => 2 < p ∧ p.Prime ∧ (skip = true → p ≠ 3)) := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (h p hp), (hS p hp).1,
          (hS p hp).2, fun hs he => hskip hs (he ▸ hp)⟩
      have hs := Finset.card_le_card sub
      rw [tab.2, hc] at hs
      omega
    obtain ⟨p,hp,hle⟩ := hp
    let U := S.erase p
    have hu : U.card = k := by simp [U, Finset.card_erase_of_mem hp, hc]
    have hus : oddFactors U := fun q h => hS _ (Finset.mem_of_mem_erase h)
    have hun : skip = true → 3 ∉ U := fun hs h => hskip hs (Finset.mem_of_mem_erase h)
    obtain ⟨hprod,hrho⟩ := ih (by omega) U hu hus hun
    have pp : (0:ℚ) < rankedPrime skip k := by exact_mod_cast (show 0 < rankedPrime skip k by omega)
    have hq : (rankedPrime skip k : ℚ) ≤ p := by exact_mod_cast hle
    have hm : 1-1/(rankedPrime skip k : ℚ) ≤ 1-1/(p:ℚ) := by
      have := one_div_le_one_div_of_le pp hq
      linarith
    have hm0 : 0 ≤ 1-1/(rankedPrime skip k : ℚ) := by
      have h1 : (1:ℚ) ≤ rankedPrime skip k := by exact_mod_cast (show 1 ≤ rankedPrime skip k by omega)
      exact sub_nonneg.mpr ((div_le_one pp).mpr h1)
    constructor
    · simpa only [rankedProd, U, Finset.prod_erase_mul S (fun q : ℕ => q) hp] using
        Nat.mul_le_mul hprod hle
    · have hr := mul_le_mul hrho hm hm0 (rho_nonneg hus)
      simpa only [rankedRho, largeRho, U,
        Finset.prod_erase_mul S (fun q : ℕ => (1:ℚ)-1/q) hp] using hr

private lemma largeRankBounds (t : ℕ) (S : Finset ℕ) (hc : S.card = 10+t)
    (hS : oddFactors S) :
    8*(10+t)*8^(10+t)+2 ≤ ∏ p ∈ S, p ∧
      (3:ℚ) ≤ ((10+t : ℕ):ℚ)*largeRho S := by
  induction t generalizing S with
  | zero =>
    have hh := ranked_bounds false 10 (by decide) S (by simpa using hc) hS (by intro h; cases h)
    constructor
    · exact (show 8*(10+0)*8^(10+0)+2 ≤ rankedProd false 10 by decide).trans hh.1
    · have nn : (3:ℚ) ≤ 10*rankedRho false 10 := by decide +kernel
      change (3:ℚ) ≤ 10*largeRho S
      linarith [hh.2]
  | succ t ih =>
    let r := 10+t
    have hr : 10 ≤ r := by dsimp [r]; omega
    have hcard : S.card = r+1 := by dsimp [r]; omega
    have hp : ∃ p ∈ S, r+1 ≤ p := by
      by_contra! h
      have sub : S ⊆ Finset.Icc 1 r := by
        intro p hp
        have hl := (hS p hp).1
        have hh := h p hp
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hs := Finset.card_le_card sub
      rw [hcard, Nat.card_Icc] at hs
      omega
    obtain ⟨p,hp,hle⟩ := hp
    let U := S.erase p
    have hu : U.card = 10+t := by simp [U, Finset.card_erase_of_mem hp, hc]
    have hus : oddFactors U := fun q h => hS _ (Finset.mem_of_mem_erase h)
    obtain ⟨hprod,hrho⟩ := ih U hu hus
    change 8*r*8^r+2 ≤ ∏ q ∈ U, q at hprod
    change (3:ℚ) ≤ (r:ℚ)*largeRho U at hrho
    have hpn : 11 ≤ p := by omega
    have hgeom : 8*(r+1)*8^(r+1)+2 ≤ (8*r*8^r+2)*11 := by
      have hcoeff : 8*(r+1) ≤ 11*r := by omega
      rw [pow_succ]
      calc
        _ ≤ 11*r*(8^r*8)+2 := Nat.add_le_add_right (Nat.mul_le_mul_right _ hcoeff) _
        _ ≤ _ := by ring_nf; omega
    constructor
    · change 8*(r+1)*8^(r+1)+2 ≤ ∏ q ∈ S, q
      have hh := hgeom.trans (Nat.mul_le_mul hprod hpn)
      simpa only [U, Finset.prod_erase_mul S (fun q : ℕ => q) hp] using hh
    · have pp : 0 < (p:ℚ) := by exact_mod_cast (show 0 < p by omega)
      have hle' : (r:ℚ)+1 ≤ p := by exact_mod_cast hle
      have frac := (div_le_one pp).mpr hle'
      have step : (r:ℚ) ≤ ((r:ℚ)+1)*(1-1/(p:ℚ)) := by
        rw [show ((r:ℚ)+1)*(1-1/(p:ℚ)) = (r:ℚ)+1-((r:ℚ)+1)/p by ring]
        linarith
      have hh := hrho.trans (mul_le_mul_of_nonneg_right step (rho_nonneg hus))
      have eqr : largeRho U*(1-1/(p:ℚ))=largeRho S :=
        Finset.prod_erase_mul S (fun q : ℕ => (1:ℚ)-1/q) hp
      change (3:ℚ) ≤ ((r+1:ℕ):ℚ)*largeRho S
      push_cast
      rw [← eqr]
      nlinarith only [hh]

private def largeCoefficient (S : Finset ℕ) : ℚ :=
  largeRho S * (29/50 + if 3 ∈ S then 2/9 else 0)

private lemma smallRankCosts {S : Finset ℕ} (hS : oddFactors S) (hnine : S.card ≤ 9) :
    (S.card ≤ 6 → (36:ℚ)/125 ≤ largeCoefficient S) ∧
    (S.card = 7 → (34:ℚ)/125 ≤ largeCoefficient S) ∧
    (8 ≤ S.card → (1:ℚ)/4 ≤ largeCoefficient S) := by
  let b : Bool := decide (3 ∉ S)
  have hskip : b = true → 3 ∉ S := fun h => of_decide_eq_true h
  have rb := (ranked_bounds b S.card (by omega) S rfl hS hskip).2
  have num : ∀ b : Bool, ∀ i : Fin 10,
      let c : ℚ := rankedRho b i.val * (29/50 + if b then 0 else 2/9)
      (i.val ≤ 6 → 36/125 ≤ c) ∧ (i.val=7 → 34/125 ≤ c) ∧
      (8 ≤ i.val → 1/4 ≤ c) := by decide +kernel
  have h0 : (0:ℚ) ≤ 29/50 + (if b then 0 else 2/9) := by
    cases b <;> norm_num
  have cc := mul_le_mul_of_nonneg_right rb h0
  have he : (if b then (0:ℚ) else 2/9) = (if 3 ∈ S then 2/9 else 0) := by
    by_cases ht : 3 ∈ S <;> simp [b, ht]
  obtain ⟨a,c,d⟩ := num b ⟨S.card,by omega⟩
  unfold largeCoefficient
  rw [← he]
  exact ⟨fun h => (a h).trans cc, fun h => (c h).trans cc, fun h => (d h).trans cc⟩

private lemma smallRankProduct {S : Finset ℕ} (hS : oddFactors S) (hnine : S.card ≤ 9) :
    (S.card = 7 → 4849845 ≤ ∏ p ∈ S, p) ∧
    (8 ≤ S.card → 111546435 ≤ ∏ p ∈ S, p) := by
  have h := (ranked_bounds false S.card (by omega) S rfl hS (by intro h; cases h)).1
  have tab : ∀ i : Fin 10,
      (i.val=7 → 4849845 ≤ rankedProd false i.val) ∧
      (8 ≤ i.val → 111546435 ≤ rankedProd false i.val) := by decide +kernel
  obtain ⟨a,b⟩ := tab ⟨S.card,by omega⟩
  exact ⟨fun hs => (a hs).trans h, fun hs => (b hs).trans h⟩

private lemma pow4_big (t : ℕ) : 100*(32*(10+t)+3) ≤ 4*4^(10+t) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 10+t.succ = (10+t)+1 by omega, pow_succ]
    omega

private lemma primeCost16 (J : ℕ) : 4*largePi (2*J+1) ≤ 4*22000+J+1 := by
  have h := large_prime_cutoff (2*J+1) 16
  rw [show (2:ℕ)^16 = 65536 by norm_num] at h
  have h' := pi_fixed
  omega

private lemma primeCost18 (J : ℕ) : 18*largePi (2*J+1) ≤ 4*J+4+18*262145 := by
  have h := large_prime_cutoff (2*J+1) 18
  rw [show (2:ℕ)^18 = 262144 by norm_num] at h
  have h' := largePi_le 262144
  omega

private def largeLoss (S : Finset ℕ) (J T : ℕ) : ℚ :=
  (largePi (2*J+1):ℚ) + (2:ℚ)^S.card*(1+2*(largePi T:ℚ)) + (J:ℚ)/T

private lemma short_budget {S : Finset ℕ} (hS : oddFactors S) {J : ℕ}
    (hj : 1000000 ≤ J) (hB : (∏ p ∈ S, p) ≤ 2*J+2) (hnine : S.card ≤ 9) :
    largeLoss S J 128 < (J:ℚ)*largeCoefficient S := by
  obtain ⟨h6,h7,h9⟩ := smallRankCosts hS hnine
  obtain ⟨p7,p9⟩ := smallRankProduct hS hnine
  have hJ0 : 0 ≤ (J:ℚ) := by positivity
  have hJr : (1000000:ℚ) ≤ J := by exact_mod_cast hj
  have cut : 4*(largePi (2*J+1):ℚ) ≤ 4*22000+(J:ℚ)+1 := by
    exact_mod_cast primeCost16 J
  unfold largeLoss
  rw [show largePi 128=30 by decide +kernel]
  by_cases hsmall : S.card ≤ 6
  · apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (h6 hsmall) hJ0)
    have powN : (2:ℕ)^S.card ≤ (2:ℕ)^6 := Nat.pow_le_pow_right (by decide) hsmall
    have powQ : (2:ℚ)^S.card ≤ 64 := by exact_mod_cast powN
    linarith
  · by_cases hseven : S.card = 7
    · apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (h7 hseven) hJ0)
      have bp := (p7 hseven).trans hB
      have hJ7 : (2400000:ℚ) ≤ J := by exact_mod_cast (show 2400000 ≤ J by omega)
      rw [hseven]
      linarith
    · have he : 8 ≤ S.card := by omega
      apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left (h9 he) hJ0)
      have bp := (p9 he).trans hB
      have hJ8 : (55000000:ℚ) ≤ J := by exact_mod_cast (show 55000000 ≤ J by omega)
      have cut18 : 18*(largePi (2*J+1):ℚ) ≤ 4*(J:ℚ)+4+18*262145 := by
        exact_mod_cast primeCost18 J
      have powN : (2:ℕ)^S.card ≤ (2:ℕ)^9 := Nat.pow_le_pow_right (by decide) hnine
      have powQ : (2:ℚ)^S.card ≤ 512 := by exact_mod_cast powN
      linarith

private lemma high_budget {S : Finset ℕ} (hS : oddFactors S) {J : ℕ}
    (hj : 1000000 ≤ J) (hB : (∏ p ∈ S, p) ≤ 2*J+2) (hten : 10 ≤ S.card) :
    16*S.card ≤ J ∧ largeLoss S J (16*S.card) < (J:ℚ)*largeCoefficient S := by
  let r := S.card
  have hr : 10 ≤ r := hten
  have hrpos : 0 < (r:ℚ) := by exact_mod_cast (show 0 < r by omega)
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hr
  have hcard : S.card = 10+t := ht
  obtain ⟨hprod,hrho⟩ := largeRankBounds t S hcard hS
  rw [← ht] at hprod hrho
  have hbase : 4*(r*8^r) ≤ J := by
    have hb := hprod.trans hB
    nlinarith only [hb]
  have hbaseQ : 4*((r:ℚ)*(8:ℚ)^r) ≤ J := by exact_mod_cast hbase
  have hJr : (1000000:ℚ) ≤ J := by exact_mod_cast hj
  have hJ0 : 0 ≤ (J:ℚ) := by positivity
  have h8 : 4 ≤ (8:ℕ)^r := by
    have hh : (8:ℕ)^1 ≤ 8^r := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  constructor
  · change 16*r ≤ J
    calc
      16*r = 4*(r*4) := by ring
      _ ≤ 4*(r*8^r) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left r h8)
      _ ≤ J := hbase
  · have hexp : (2:ℕ)^(3*r) = 8^r := by rw [pow_mul] <;> rfl
    have cut := large_prime_cutoff (2*J+1) (3*r)
    rw [hexp] at cut
    have small := Nat.mul_le_mul_left (3*r) (largePi_le (8^r))
    have cutN : 3*(r*largePi (2*J+1)) ≤ 4*J+2+3*(r*8^r) := by
      nlinarith only [cut,small]
    have cutQ : 3*((r:ℚ)*(largePi (2*J+1):ℚ)) ≤ 4*(J:ℚ)+2+3*((r:ℚ)*(8:ℚ)^r) := by
      exact_mod_cast cutN
    have pbound : (r:ℚ)*(largePi (2*J+1):ℚ) ≤ (8/5:ℚ)*J := by linarith
    have hstep := pow4_big t
    rw [← ht] at hstep
    have hsmall : 1+2*largePi (16*r) ≤ 32*r+3 := by
      have := largePi_le (16*r)
      omega
    have herrN : 100*r*2^r*(1+2*largePi (16*r)) ≤ J := calc
      _ ≤ 100*r*2^r*(32*r+3) := Nat.mul_le_mul_left _ hsmall
      _ = (r*2^r)*(100*(32*r+3)) := by ring
      _ ≤ (r*2^r)*(4*4^r) := Nat.mul_le_mul_left _ hstep
      _ = 4*(r*8^r) := by
        rw [show (8:ℕ)^r = 2^r*4^r by rw [← mul_pow] <;> rfl]
        ring
      _ ≤ J := hbase
    have herr : 100*(r:ℚ)*(2:ℚ)^r*(1+2*(largePi (16*r):ℚ)) ≤ J := by exact_mod_cast herrN
    have main : (87/50:ℚ) ≤ (r:ℚ)*largeCoefficient S := by
      unfold largeCoefficient
      by_cases h3 : 3 ∈ S
      · rw [if_pos h3]
        nlinarith only [hrho]
      · rw [if_neg h3]
        nlinarith only [hrho]
    apply lt_of_not_ge
    intro hcontra
    apply not_lt_of_ge (mul_le_mul_of_nonneg_left hcontra hrpos.le)
    change (r:ℚ)*((largePi (2*J+1):ℚ)+(2:ℚ)^r*(1+2*(largePi (16*r):ℚ))+
        (J:ℚ)/((16*r:ℕ):ℚ)) < (r:ℚ)*((J:ℚ)*largeCoefficient S)
    have htail : (r:ℚ)*((J:ℚ)/((16*r:ℕ):ℚ)) = (J:ℚ)/16 := by
      push_cast
      field_simp [hrpos.ne'] <;> ring
    have hm := mul_le_mul_of_nonneg_right main hJ0
    nlinarith only [htail, hJr, pbound, herr, hm]

/-- The fixed cutoff through rank nine and a linear cutoff thereafter
make the sieve loss strictly smaller than the retained main term. -/
theorem large_sieve_budget {S : Finset ℕ} {J : ℕ} (hJ : 1000000 ≤ J)
    (hS : ∀ p ∈ S, 2 < p ∧ p.Prime) (hB : (∏ p ∈ S, p) ≤ 2*J+2) :
    ∃ T : ℕ, 1 ≤ T ∧ T ≤ J ∧
      (largePi (2*J+1):ℚ) + (2:ℚ)^S.card*(1+2*(largePi T:ℚ))+(J:ℚ)/T <
      (J:ℚ)*(largeRho S*(29/50 + if 3 ∈ S then 2/9 else 0)) := by
  by_cases h : S.card ≤ 9
  · exact ⟨128,by decide,by omega,short_budget hS hJ hB h⟩
  · have hh := high_budget hS hJ hB (by omega)
    exact ⟨16*S.card,by omega,hh.1,hh.2⟩

end A085265Sieve

namespace A085265InclusionExclusion

/-- Repeatedly subtract the contribution of multiples of the next divisor. -/
def sift (ps : List ℕ) (F : ℕ → ℚ) (d : ℕ) : ℚ :=
  match ps with
  | [] => F d
  | p :: rest => sift rest F d - sift rest F (d*p)

def density (ps : List ℕ) : ℚ :=
  (ps.map fun p => 1 - 1 / (p : ℚ)).prod

theorem sift_main (ps : List ℕ) (X : ℚ) (d : ℕ) :
    sift ps (fun t => X / (t : ℚ)) d = X / d * density ps := by
  induction ps generalizing d with
  | nil => simp [sift, density]
  | cons p rest ih =>
    change sift rest (fun t => X / (t : ℚ)) d -
      sift rest (fun t => X / (t : ℚ)) (d*p) = _
    rw [ih d, ih (d*p)]
    change X / (d : ℚ) * density rest - X / ((d*p : ℕ) : ℚ) * density rest =
      X / (d : ℚ) * ((1 - 1 / (p : ℚ)) * density rest)
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring

theorem sift_shift (ps : List ℕ) (F : ℕ → ℚ) (c : ℚ) (d : ℕ) :
    sift ps (fun t => F t + c) d = sift ps F d + (if ps = [] then c else 0) := by
  induction ps generalizing d with
  | nil => simp [sift]
  | cons p rest ih => simp [sift, ih] <;> ring

/-- A pointwise unit error for each squarefree divisor contributes at most one
unit for each subset of the prime divisors. Only divisors of d times the
listed product are needed. -/
theorem sift_error (ps : List ℕ) (F H : ℕ → ℚ) (E : ℚ) (d : ℕ)
    (h : ∀ t : ℕ, t ∣ d*ps.prod → |F t - H t| ≤ E) :
    |sift ps F d - sift ps H d| ≤ (2:ℚ)^ps.length * E := by
  induction ps generalizing d with
  | nil => simpa [sift] using h d (by simp)
  | cons p rest ih =>
    have hd : d * rest.prod ∣ d * (p :: rest).prod := ⟨p, by simp only [List.prod_cons]; ring⟩
    have hleft := ih d (fun t ht => h t (ht.trans hd))
    have hright := ih (d*p) (fun t ht => h t (by simpa [Nat.mul_assoc] using ht))
    obtain ⟨hl, hu⟩ := abs_le.mp hleft
    obtain ⟨hl', hu'⟩ := abs_le.mp hright
    simp only [sift, List.length_cons, pow_succ]
    apply abs_le.mpr
    constructor <;> linarith

theorem sift_sum {α : Type*} (s : Finset α) (ps : List ℕ) (F : α → ℕ → ℚ) (d : ℕ) :
    sift ps (fun t => ∑ x ∈ s, F x t) d = ∑ x ∈ s, sift ps (F x) d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p rest ih => simp only [sift, ih, Finset.sum_sub_distrib]

/-- Sieving the indicator of divisibility gives the indicator of divisibility
and coprimality to the sieving product. -/
theorem sift_indicator (ps : List ℕ) (x d : ℕ) (hpair : ps.Pairwise Nat.Coprime)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hd : ∀ p ∈ ps, d.Coprime p) :
    sift ps (fun t => if t ∣ x then 1 else 0) d =
      if d ∣ x ∧ ps.prod.Coprime x then 1 else 0 := by
  induction ps generalizing d with
  | nil => simp [sift]
  | cons p rest ih =>
    obtain ⟨hpr, hr⟩ := List.pairwise_cons.mp hpair
    have hprime := hp p (by simp)
    have hdp := hd p (by simp)
    have hprimes : ∀ q ∈ rest, Nat.Prime q := fun q hq => hp q (by simp [hq])
    have hcop : ∀ q ∈ rest, d.Coprime q := fun q hq => hd q (by simp [hq])
    have hcop' : ∀ q ∈ rest, (d*p).Coprime q := fun q hq =>
      (hcop q hq).mul_left (hpr q hq)
    have hmul : d*p ∣ x ↔ d ∣ x ∧ p ∣ x := by
      constructor
      · intro hh
        exact ⟨(Nat.dvd_mul_right d p).trans hh, (Nat.dvd_mul_left p d).trans hh⟩
      · rintro ⟨h1,h2⟩
        exact hdp.mul_dvd_of_dvd_of_dvd h1 h2
    simp only [sift, ih d hr hprimes hcop, ih (d*p) hr hprimes hcop',
      List.prod_cons, Nat.coprime_mul_iff_left, hprime.coprime_iff_not_dvd, hmul]
    by_cases h1 : d ∣ x <;> by_cases h2 : p ∣ x <;> by_cases h3 : rest.prod.Coprime x <;>
      simp [h1,h2,h3]

/-- In particular, if the number of multiples of each d in a candidate set
is within E of X/d, imposing coprimality changes the main term to X times
the proportion of units, with error at most 2^r times E. -/
theorem coprime_values_error_centered {α : Type*} (s : Finset α) (v : α → ℕ)
    (ps : List ℕ) (X c E : ℚ)
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (h : ∀ d : ℕ, d ∣ ps.prod →
      |(∑ x ∈ s, if d ∣ v x then (1:ℚ) else 0) - (X/d + c)| ≤ E) :
    |(∑ x ∈ s, if ps.prod.Coprime (v x) then (1:ℚ) else 0)
        - (X * density ps + if ps = [] then c else 0)|
      ≤ (2:ℚ)^ps.length * E := by
  have bound := sift_error ps (fun d => ∑ x ∈ s, if d ∣ v x then (1:ℚ) else 0)
    (fun t => X / (t : ℚ) + c) E 1 (fun t ht => h t (by simpa using ht))
  rw [sift_sum, sift_shift, sift_main] at bound
  have hind (x : ℕ) : sift ps (fun t => if t ∣ x then 1 else 0) 1 =
      if ps.prod.Coprime x then 1 else 0 := by
    simpa using sift_indicator ps x 1 hpair hp (fun p _ => Nat.coprime_one_left p)
  simpa only [hind, Nat.cast_one, div_one] using bound

theorem coprime_count_error_centered (s : Finset ℕ) (ps : List ℕ) (X c E : ℚ)
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (h : ∀ d : ℕ, d ∣ ps.prod →
      |(∑ x ∈ s, if d ∣ x then (1:ℚ) else 0) - (X/d + c)| ≤ E) :
    |(∑ x ∈ s, if ps.prod.Coprime x then (1:ℚ) else 0)
        - (X * density ps + if ps = [] then c else 0)|
      ≤ (2:ℚ)^ps.length * E :=
  coprime_values_error_centered s id ps X c E hpair hp h

theorem coprime_count_error (s : Finset ℕ) (ps : List ℕ) (X E : ℚ)
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (h : ∀ d : ℕ, d ∣ ps.prod →
      |(∑ x ∈ s, if d ∣ x then (1:ℚ) else 0) - X/d| ≤ E) :
    |(∑ x ∈ s, if ps.prod.Coprime x then (1:ℚ) else 0) - X * density ps|
      ≤ (2:ℚ)^ps.length * E := by
  simpa using coprime_count_error_centered s ps X 0 E hpair hp (by simpa using h)

end A085265InclusionExclusion

namespace A085265InclusionExclusion

/-- Count the progression r, r+m, ... strictly below J. -/
theorem residue_card (m J r : ℕ) (hm : 0 < m) (hr : r < m) :
    ((Finset.range J).filter (fun x => x % m = r)).card =
      J/m + if r < J%m then 1 else 0 := by
  let c := J/m + if r < J%m then 1 else 0
  let f (i : ℕ) := r+i*m
  have hJ := Nat.div_add_mod' J m
  have hrem := Nat.mod_lt J hm
  have hlt (i : ℕ) : i < c ↔ f i < J := by
    dsimp [c,f]
    rcases lt_trichotomy i (J/m) with hi | he | hi
    · have hg : (i+1)*m ≤ (J/m)*m := Nat.mul_le_mul_right m hi
      rw [Nat.add_mul, one_mul] at hg
      split_ifs <;> omega
    · rw [he]
      split_ifs <;> omega
    · have hg : (J/m+1)*m ≤ i*m := Nat.mul_le_mul_right m hi
      rw [Nat.add_mul, one_mul] at hg
      split_ifs <;> omega
  have hs : (Finset.range J).filter (fun x => x % m = r) = (Finset.range c).image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
      have hv : f (x/m) = x := by
        have hv := Nat.mod_add_div' x m
        simpa only [f,he] using hv
      exact Finset.mem_image.mpr ⟨x/m, Finset.mem_range.mpr
        ((hlt _).mpr (by rw [hv]; exact Finset.mem_range.mp hx)), hv⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((hlt i).mp (Finset.mem_range.mp hi)),
        by simp [f,Nat.add_mod,Nat.mod_eq_of_lt hr]⟩
  have hf : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    have he : i*m = j*m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm he
  rw [hs, Finset.card_image_of_injective _ hf, Finset.card_range]

/-- If the smaller representative is in the first half of a complete block and
the larger in the second, their combined count differs from 2J/m by at most one.
The residues here are indexed from zero, so x corresponds to the index j=x+1. -/
theorem paired_residue_error (m J a b : ℕ) (hm : 0 < m) (hab : a < b) (hb : b < m)
    (haHalf : 2*a ≤ m) (hbHalf : m ≤ 2*(b+1)) :
    |(((Finset.range J).filter (fun x => x%m=a)).card : ℚ) +
      (((Finset.range J).filter (fun x => x%m=b)).card : ℚ) - 2*J/m| ≤ 1 := by
  rw [residue_card m J a hm (hab.trans hb), residue_card m J b hm hb]
  let e : ℕ := (if a < J%m then 1 else 0) + (if b < J%m then 1 else 0)
  have hrem := Nat.mod_lt J hm
  have hsmall : 2*(J%m) ≤ (e+1)*m ∧ e*m ≤ 2*(J%m)+m := by
    dsimp [e]
    split_ifs <;> constructor <;> omega
  let C := (J/m + if a < J%m then 1 else 0) + (J/m + if b < J%m then 1 else 0)
  have hc : C = 2*(J/m)+e := by
    dsimp [C,e]
    omega
  have hJ := Nat.div_add_mod' J m
  have hlow : 2*J ≤ (C+1)*m := by rw [hc]; nlinarith [hsmall.1]
  have hhigh : C*m ≤ 2*J+m := by rw [hc]; nlinarith [hsmall.2]
  have low : 2*(J:ℚ) ≤ ((C:ℚ)+1)*(m:ℚ) := by exact_mod_cast hlow
  have high : (C:ℚ)*(m:ℚ) ≤ 2*(J:ℚ)+(m:ℚ) := by exact_mod_cast hhigh
  have hm' : (0:ℚ) < m := by exact_mod_cast hm
  have h1 := (div_le_iff₀ hm').mpr low
  have h2 : (C:ℚ)-1 ≤ 2*(J:ℚ)/(m:ℚ) :=
    (le_div_iff₀ hm').mpr (by linarith)
  have hfinal : |(C:ℚ)-2*(J:ℚ)/(m:ℚ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [C, Nat.cast_add] using hfinal

end A085265InclusionExclusion

namespace A085265InclusionExclusion

private theorem dvd_double_rem (d x b : ℕ) :
    d ∣ 2*x+b ↔ d ∣ 2*(x%d)+b := by
  have hx := Nat.div_add_mod' x d
  have he : 2*x+b = (2*(x/d))*d + (2*(x%d)+b) := by nlinarith
  rw [he]
  exact Nat.dvd_add_right (Nat.dvd_mul_left d _)

private theorem odd_divisor_even_roots {d : ℕ} (hd : Odd d) (x : ℕ) :
    d ∣ 2*x+2 ↔ x%d=d-1 := by
  obtain ⟨v,hv⟩ := hd
  have hdpos : 0 < d := by omega
  have hrem := Nat.mod_lt x hdpos
  rw [dvd_double_rem]
  constructor
  · intro h
    by_contra hne
    have hh := Nat.eq_of_dvd_of_lt_two_mul (by omega : 2*(x%d)+2 ≠ 0) h (by omega)
    omega
  · intro he
    refine ⟨2, ?_⟩
    omega

private theorem odd_divisor_odd_roots {d v : ℕ} (hv : d=2*v+1) (x : ℕ) :
    d ∣ 2*x+1 ↔ x%d=v := by
  have hdpos : 0 < d := by omega
  have hrem := Nat.mod_lt x hdpos
  rw [dvd_double_rem]
  constructor
  · intro h
    have hh := Nat.eq_of_dvd_of_lt_two_mul (by omega : 2*(x%d)+1 ≠ 0) h (by omega)
    omega
  · intro he
    rw [he, ← hv]

/-- The initial progression of even roots has an error of at most one half
after centering its main term by subtracting one half. -/
theorem even_divisor_error {d : ℕ} (hd : Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if d ∣ 2*x+2 then (1:ℚ) else 0) -
      ((J:ℚ)/d - 1/2)| ≤ 1/2 := by
  obtain ⟨v,hv⟩ := hd
  have hdpos : 0 < d := by omega
  have hr := Nat.mod_lt J hdpos
  have hn : ¬ d-1 < J%d := by omega
  simp_rw [odd_divisor_even_roots (show Odd d from ⟨v,hv⟩)]
  rw [Finset.sum_boole, residue_card d J (d-1) hdpos (by omega), if_neg hn, Nat.add_zero]
  have hJ := Nat.div_add_mod' J d
  have hlow : ((J/d:ℕ):ℚ)*(d:ℚ) ≤ J := by
    exact_mod_cast (show (J/d)*d ≤ J by omega)
  have hhigh : (J:ℚ) ≤ (((J/d:ℕ):ℚ)+1)*(d:ℚ) := by
    exact_mod_cast (show J ≤ (J/d+1)*d by rw [Nat.add_mul,one_mul]; omega)
  have hpos : (0:ℚ) < d := by exact_mod_cast hdpos
  have h1 := (le_div_iff₀ hpos).mpr hlow
  have h2 := (div_le_iff₀ hpos).mpr hhigh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- In the odd progression the admissible class is centered in every block. -/
theorem odd_divisor_error {d : ℕ} (hd : Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if d ∣ 2*x+1 then (1:ℚ) else 0) -
      (J:ℚ)/d| ≤ 1/2 := by
  obtain ⟨v,hv⟩ := hd
  have hdv : d=2*v+1 := by omega
  have hdpos : 0 < d := by omega
  have hr := Nat.mod_lt J hdpos
  have hJ := Nat.div_add_mod' J d
  simp_rw [odd_divisor_odd_roots hdv]
  rw [Finset.sum_boole, residue_card d J v hdpos (by omega)]
  let C := J/d + if v < J%d then 1 else 0
  have hlow : 2*J ≤ (2*C+1)*d := by
    dsimp [C]
    split_ifs with ht
    · nlinarith
    · nlinarith
  have hhigh : 2*C*d ≤ 2*J+d := by
    dsimp [C]
    split_ifs with ht
    · nlinarith
    · simp only [Nat.add_zero, Nat.mul_assoc]
      omega
  have hl : 2*(J:ℚ) ≤ (2*(C:ℚ)+1)*(d:ℚ) := by exact_mod_cast hlow
  have hu : 2*(C:ℚ)*(d:ℚ) ≤ 2*(J:ℚ)+(d:ℚ) := by exact_mod_cast hhigh
  have hpos : (0:ℚ) < d := by exact_mod_cast hdpos
  have h1 : (J:ℚ)/d ≤ (C:ℚ)+1/2 := (div_le_iff₀ hpos).mpr (by nlinarith only [hl])
  have h2 : (C:ℚ)-1/2 ≤ (J:ℚ)/d := (le_div_iff₀ hpos).mpr (by nlinarith only [hu])
  change |(C:ℚ)-(J:ℚ)/d| ≤ 1/2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem initial_even_coprime (ps : List ℕ) (hne : ps ≠ [])
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (hd : ∀ d : ℕ, d ∣ ps.prod → Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if ps.prod.Coprime (2*x+2) then (1:ℚ) else 0) -
      (J:ℚ)*density ps| ≤ (2:ℚ)^ps.length / 2 := by
  have h := coprime_values_error_centered (Finset.range J) (fun x => 2*x+2) ps J
    (-(1/2)) (1/2) hpair hp (fun d hf => by
      simpa only [sub_eq_add_neg] using even_divisor_error (hd d hf) J)
  simpa [hne,div_eq_mul_inv] using h

theorem initial_odd_coprime (ps : List ℕ) (hpair : ps.Pairwise Nat.Coprime)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hd : ∀ d : ℕ, d ∣ ps.prod → Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if ps.prod.Coprime (2*x+1) then (1:ℚ) else 0) -
      (J:ℚ)*density ps| ≤ (2:ℚ)^ps.length / 2 := by
  have h := coprime_values_error_centered (Finset.range J) (fun x => 2*x+1) ps J
    0 (1/2) hpair hp (fun d hf => by simpa using odd_divisor_error (hd d hf) J)
  simpa [div_eq_mul_inv] using h

end A085265InclusionExclusion

namespace A085265InclusionExclusion

/-- An affine progression of step two visits each class of an odd modulus
once per period. -/
private theorem affine_residue (m b c : ℕ) (hm : Odd m) :
    ∃ a < m, ∀ x : ℕ, (2*x+b ≡ c [MOD m]) ↔ x % m = a := by
  obtain ⟨t,ht⟩ := hm
  letI : NeZero m := ⟨by omega⟩
  let i : ZMod m := ((t+1:ℕ) : ZMod m)
  have hinv : 2*i=1 := by
    have he : 2*(t+1)=m+1 := by omega
    calc
      2*i = ((2*(t+1):ℕ):ZMod m) := by simp [i]
      _ = 1 := by rw [he]; simp
  let z : ZMod m := i*((c:ZMod m) - b)
  refine ⟨z.val, ZMod.val_lt z, ?_⟩
  intro x
  have hcast : (2*x+b ≡ c [MOD m]) ↔ 2*(x:ZMod m)+b=(c:ZMod m) := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast <;> rfl
  have hval : (x:ZMod m)=z ↔ x%m=z.val := by
    calc
      (x:ZMod m)=z ↔ (x:ZMod m)=(z.val:ZMod m) := by rw [ZMod.natCast_zmod_val]
      _ ↔ x%m=z.val := by
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (ZMod.val_lt z)]
  rw [hcast, ← hval]
  constructor
  · intro h
    dsimp [z]
    calc
      (x:ZMod m) = (2*i)*x := by rw [hinv,one_mul]
      _ = i*((c:ZMod m)-b) := by linear_combination i*h
  · intro hx
    rw [hx]
    dsimp [z]
    calc
      2*(i*((c:ZMod m)-b))+b = (2*i)*((c:ZMod m)-b)+b := by ring
      _ = c := by rw [hinv]; ring

/-- Combining a divisibility condition with one residue modulo Q gives one
class of the index modulo dQ. -/
theorem affine_crt_class (d Q b s : ℕ) (hc : d.Coprime Q) (ho : Odd (d*Q)) :
    ∃ a < d*Q, ∀ x : ℕ, (d ∣ 2*x+b ∧ 2*x+b ≡ s [MOD Q]) ↔ x%(d*Q)=a := by
  let c := Nat.chineseRemainder hc 0 s
  obtain ⟨a,ha,he⟩ := affine_residue (d*Q) b c.val ho
  refine ⟨a,ha,?_⟩
  intro x
  rw [← he x, ← Nat.modEq_and_modEq_iff_modEq_mul hc, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun ⟨h1,h2⟩ => ⟨h1.trans c.property.1.symm,h2.trans c.property.2.symm⟩,
    fun ⟨h1,h2⟩ => ⟨h1.trans c.property.1,h2.trans c.property.2⟩⟩

theorem one_residue_error {m a : ℕ} (hm : 0 < m) (ha : a < m) (J : ℕ) :
    |(((Finset.range J).filter (fun x => x%m=a)).card : ℚ)-(J:ℚ)/m| ≤ 1 := by
  rw [residue_card m J a hm ha]
  have hJ := Nat.div_add_mod' J m
  have hr := Nat.mod_lt J hm
  have hl : ((J/m:ℕ):ℚ)*(m:ℚ) ≤ (J:ℚ) := by
    exact_mod_cast (show (J/m)*m ≤ J by omega)
  have hu : (J:ℚ) ≤ (((J/m:ℕ):ℚ)+1)*(m:ℚ) := by
    exact_mod_cast (show J ≤ (J/m+1)*m by rw [Nat.add_mul,one_mul]; omega)
  have hpos : (0 : ℚ) < m := by exact_mod_cast hm
  have hlow := (le_div_iff₀ hpos).mpr hl
  have hhigh := (div_le_iff₀ hpos).mpr hu
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> linarith

/-- The sifted count in any one root class is within 2^r of its main term.
Summing twice gives the error term used by the large-J budget. -/
theorem congruence_loss (ps : List ℕ) (J Q s b : ℕ) (hpair : ps.Pairwise Nat.Coprime)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hcrt : ∀ d : ℕ, d ∣ ps.prod → d.Coprime Q ∧ Odd (d*Q)) :
    |(∑ x ∈ (Finset.range J).filter (fun x => 2*x+b ≡ s [MOD Q]),
      if ps.prod.Coprime (2*x+b) then (1:ℚ) else 0) - (J:ℚ)/Q*density ps|
      ≤ (2:ℚ)^ps.length := by
  let S := (Finset.range J).filter (fun x => 2*x+b ≡ s [MOD Q])
  have loc (d : ℕ) (hd : d ∣ ps.prod) :
      |(∑ x ∈ S, if d ∣ 2*x+b then (1:ℚ) else 0) - (((J:ℚ)/Q)/d + 0)| ≤ 1 := by
    obtain ⟨hc,ho⟩ := hcrt d hd
    obtain ⟨a,ha,he⟩ := affine_crt_class d Q b s hc ho
    have eqs : S.filter (fun x => d ∣ 2*x+b) =
        (Finset.range J).filter (fun x => x%(d*Q)=a) := by
      ext x
      simp only [S,Finset.mem_filter]
      rw [← he x]
      tauto
    rw [Finset.sum_boole,eqs,add_zero,div_div]
    have hden : (Q:ℚ)*(d:ℚ) = ((d*Q:ℕ):ℚ) := by push_cast; ring
    rw [hden]
    exact one_residue_error (by omega) ha J
  have h := coprime_values_error_centered S (fun x => 2*x+b) ps ((J:ℚ)/Q) 0 1
    hpair hp loc
  simpa [S] using h

end A085265InclusionExclusion

namespace A085265InclusionExclusion

def primeRoots (n p : ℕ) := (Finset.range (p^2)).filter (fun r => r^2 ≡ n [MOD p^2])

/-- Below the modulus the two roots are an opposite pair. The assumption
that p² does not divide n suffices, including primes dividing n exactly once. -/
private theorem root_or_opposite {n p a b : ℕ}
    (hp : p.Prime) (hp2 : 2<p) (hn : ¬p^2 ∣ n) (hab : a≤b)
    (ha : a^2 ≡ n [MOD p^2]) (hb : b^2 ≡ n [MOD p^2]) :
    p^2 ∣ b-a ∨ p^2 ∣ a+b := by
  let d := b-a
  have hba : b=a+d := by dsimp [d]; omega
  have hs : b^2=a^2+d*(a+b) := by rw [hba]; ring
  have hdiv := (ha.trans hb.symm).dvd'
  rw [hs,Nat.add_sub_cancel_left] at hdiv
  by_cases hd : p ∣ d
  · left
    have hcop : p.Coprime (a+b) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hu
      have h2a : p ∣ 2*a := by
        have he : a+b-d=2*a := by omega
        simpa only [he] using Nat.dvd_sub hu hd
      have hpa : p ∣ a := (hp.dvd_mul.mp h2a).resolve_left
        (fun h => (not_le.mpr hp2) (Nat.le_of_dvd (by decide) h))
      obtain ⟨t,ht⟩ := hpa
      have haa : p^2 ∣ a^2 := ⟨t^2,by rw [ht]; ring⟩
      exact hn (Nat.modEq_zero_iff_dvd.mp (ha.symm.trans haa.modEq_zero_nat))
    exact (hcop.pow_left 2).dvd_of_dvd_mul_right hdiv
  · right
    exact ((hp.coprime_iff_not_dvd.mpr hd).pow_left 2).dvd_of_dvd_mul_left hdiv

theorem primeRoots_card {n p : ℕ} (hp : p.Prime) (hp2 : 2<p) (hn : ¬p^2 ∣ n) :
    (primeRoots n p).card ≤ 2 := by
  classical
  by_cases hs : (primeRoots n p).Nonempty
  · obtain ⟨s,hs⟩ := hs
    obtain ⟨hsr,hsq⟩ := Finset.mem_filter.mp hs
    have slt := Finset.mem_range.mp hsr
    have sp : 0<s := by
      by_contra! hz
      have : s=0 := by omega
      subst s
      apply hn
      exact Nat.modEq_zero_iff_dvd.mp (by simpa using hsq.symm)
    have sub : primeRoots n p ⊆ {s,p^2-s} := by
      intro z hz
      obtain ⟨hzr,hzq⟩ := Finset.mem_filter.mp hz
      have zlt := Finset.mem_range.mp hzr
      have half {a b : ℕ} (hab : a ≤ b) (ha : a^2 ≡ n [MOD p^2])
          (hb : b^2 ≡ n [MOD p^2]) (blt : b<p^2) (hpos : 0<a+b) :
          a=b ∨ a+b=p^2 := by
        rcases root_or_opposite hp hp2 hn hab ha hb with hd | hsum
        · left
          by_contra hne
          have := Nat.le_of_dvd (show 0<b-a by omega) hd
          omega
        · exact Or.inr (Nat.eq_of_dvd_of_lt_two_mul (by omega) hsum (by omega))
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rcases le_total z s with h | h
      · rcases half h hzq hsq slt (by omega) with he | he <;> omega
      · rcases half h hsq hzq zlt (by omega) with he | he <;> omega
    calc
      _ ≤ ({s,p^2-s} : Finset ℕ).card := Finset.card_le_card sub
      _ ≤ 2 := Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Candidates have the form 2x+b, where x starts at zero and b=1 or 2.
The entire bin [t p²,(t+1)p²) contains at most one candidate root. -/
theorem raw_prime_loss {n p b J : ℕ} (hp : p.Prime) (hp2 : 2<p) (hn : ¬p^2 ∣ n)
    (hb : b ≤ 2) :
    ((Finset.range J).filter (fun x => (2*x+b)^2 ≡ n [MOD p^2])).card ≤ 2*J/(p^2)+1 := by
  let A := (Finset.range J).filter (fun x => (2*x+b)^2 ≡ n [MOD p^2])
  let f (x : ℕ) := (2*x+b)/(p^2)
  let bins := Finset.range (2*J/(p^2)+1)
  have hm : 0<p^2 := pow_pos hp.pos 2
  have hcop : (p^2).Coprime 2 := ((hp.odd_of_ne_two (by omega)).pow.coprime_two_left).symm
  have inj {x y : ℕ} (hx : x∈A) (hy : y∈A) (hxy : x≤y) (hf : f x=f y) : x=y := by
    have hs := root_or_opposite hp hp2 hn (show 2*x+b ≤ 2*y+b by omega)
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    change (2*x+b)/(p^2)=(2*y+b)/(p^2) at hf
    by_contra hne
    have bounds {L M : ℕ} (lo : L ≤ 2*x+b) (hi : 2*y+b < L+M) :
        (0 < y-x ∧ y-x < M) ∧ (0 < x+y+b-L ∧ x+y+b-L < M) := by omega
    have hi : 2*y+b < ((2*x+b)/(p^2))*(p^2) + p^2 := by
      calc
        2*y+b < (p^2)*((2*y+b)/(p^2)+1) := Nat.lt_mul_div_succ _ hm
        _ = _ := by rw [← hf]; ring
    obtain ⟨hdiff,hmid⟩ := bounds (Nat.div_mul_le_self (2*x+b) (p^2)) hi
    rcases hs with hd | hsum
    · have he : 2*y+b-(2*x+b)=2*(y-x) := by omega
      rw [he] at hd
      exact (Nat.not_le_of_lt hdiff.2) (Nat.le_of_dvd hdiff.1 (hcop.dvd_of_dvd_mul_left hd))
    · have he : (2*x+b)+(2*y+b)=2*(x+y+b) := by omega
      rw [he] at hsum
      have hv := hcop.dvd_of_dvd_mul_left hsum
      have hbase : p^2 ∣ ((2*x+b)/(p^2))*(p^2) := Nat.dvd_mul_left _ _
      have hh := Nat.dvd_sub hv hbase
      exact (Nat.not_le_of_lt hmid.2) (Nat.le_of_dvd hmid.1 hh)
  have hc : A.card ≤ bins.card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (show 2*x+b ≤ 2*J by omega)))
    · intro x hx y hy he
      rcases le_total x y with h | h
      · exact inj hx hy h he
      · exact (inj hy hx h he.symm).symm
  simpa only [A,bins,Finset.card_range] using hc

end A085265InclusionExclusion

namespace A085265InclusionExclusion

def candidateSet (ps : List ℕ) (J b : ℕ) :=
  (Finset.range J).filter (fun x => ps.prod.Coprime (2*x+b))

def hitSet (n p : ℕ) (ps : List ℕ) (J b : ℕ) :=
  (candidateSet ps J b).filter (fun x => (2*x+b)^2 ≡ n [MOD p^2])

theorem hit_card_raw {n p b J : ℕ} (ps : List ℕ) (hp : p.Prime) (hp2 : 2<p)
    (hn : ¬p^2 ∣ n) (hb : b≤2) : (hitSet n p ps J b).card ≤ 2*J/(p^2)+1 := by
  apply le_trans (Finset.card_le_card ?_) (raw_prime_loss hp hp2 hn hb)
  intro x hx
  obtain ⟨hx,hcon⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hcon⟩

theorem hit_card_sifted {n p : ℕ} (ps : List ℕ) (J b : ℕ)
    (hp : p.Prime) (hp2 : 2<p) (hn : ¬p^2 ∣ n)
    (hpair : ps.Pairwise Nat.Coprime) (hps : ∀ q ∈ ps, Nat.Prime q) (hrho : 0≤density ps)
    (hcrt : ∀ d : ℕ, d ∣ ps.prod → d.Coprime (p^2) ∧ Odd (d*p^2)) :
    ((hitSet n p ps J b).card : ℚ) ≤ 2*((J:ℚ)/(p^2)*density ps + 2^ps.length) := by
  classical
  let piece (s : ℕ) := ((Finset.range J).filter (fun x => 2*x+b ≡ s [MOD p^2])).filter
    (fun x => ps.prod.Coprime (2*x+b))
  have hsub : hitSet n p ps J b ⊆ (primeRoots n p).biUnion piece := by
    intro x hx
    obtain ⟨hc,hxq⟩ := Finset.mem_filter.mp hx
    obtain ⟨hr,hpc⟩ := Finset.mem_filter.mp hc
    let u := 2*x+b
    let s := u%(p^2)
    have hsu : s ≡ u [MOD p^2] := Nat.mod_modEq u (p^2)
    have hsr : s ∈ primeRoots n p := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos hp.pos 2)), (hsu.pow 2).trans hxq⟩
    exact Finset.mem_biUnion.mpr ⟨s,hsr,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hr,hsu.symm⟩,hpc⟩⟩
  have hcards : (hitSet n p ps J b).card ≤ ∑ s ∈ primeRoots n p, (piece s).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  let cost : ℚ := (J:ℚ)/(p^2)*density ps + 2^ps.length
  have hpiece (s : ℕ) : ((piece s).card:ℚ) ≤ cost := by
    have h := (abs_le.mp (congruence_loss ps J (p^2) s b hpair hps hcrt)).2
    rw [Finset.sum_boole] at h
    push_cast at h
    change ((piece s).card:ℚ) - (J:ℚ)/(p:ℚ)^2*density ps ≤ 2^ps.length at h
    dsimp [cost]
    linarith
  calc
    ((hitSet n p ps J b).card : ℚ) ≤ ∑ s ∈ primeRoots n p, ((piece s).card:ℚ) := by
      exact_mod_cast hcards
    _ ≤ ∑ _s ∈ primeRoots n p, cost := Finset.sum_le_sum (fun s _ => hpiece s)
    _ = ((primeRoots n p).card:ℚ)*cost := by simp
    _ ≤ 2*cost := mul_le_mul_of_nonneg_right (by exact_mod_cast primeRoots_card hp hp2 hn)
      (by dsimp [cost]; positivity)

end A085265InclusionExclusion

namespace A085265InclusionExclusion

open A085265Sieve

structure PrimeEnumeration (S : Finset ℕ) where
  ps : List ℕ
  pair : ps.Pairwise Nat.Coprime
  mem : ∀ p, p ∈ ps ↔ p ∈ S
  len : ps.length = S.card
  product : ps.prod = ∏ p ∈ S, p
  rho : density ps = largeRho S

theorem prime_enumeration (S : Finset ℕ) (hS : ∀ p ∈ S, 2<p ∧ p.Prime) :
    Nonempty (PrimeEnumeration S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⟨[],by simp,by simp,by simp,by simp,by simp [density,largeRho]⟩⟩
  | @insert a S ha ih =>
    obtain ⟨D⟩ := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    have hpa := (hS a (Finset.mem_insert_self a S)).2
    refine ⟨⟨a::D.ps, List.pairwise_cons.mpr ⟨?_,D.pair⟩, ?_, ?_, ?_, ?_⟩⟩
    · intro q hq
      have hqm := (D.mem q).mp hq
      exact (Nat.coprime_primes hpa (hS q (Finset.mem_insert_of_mem hqm)).2).mpr (by
        rintro rfl; exact ha hqm)
    · intro p
      simp [D.mem]
    · simp [ha,D.len]
    · simp [ha,D.product]
    · change (1 - 1 / (a : ℚ)) * density D.ps = largeRho (insert a S)
      rw [D.rho]
      simp only [largeRho, Finset.prod_insert ha]

private theorem odd_product_list (ps : List ℕ) (h : ∀ p ∈ ps, Odd p) : Odd ps.prod := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    exact (h p (by simp)).mul (ih (fun q hq => h q (by simp [hq])))

private theorem cop_product_list (ps : List ℕ) (p : ℕ) (h : ∀ q ∈ ps, q.Coprime p) :
    ps.prod.Coprime p := by
  induction ps with
  | nil => simp
  | cons q rest ih =>
    exact (h q (by simp)).mul_left (ih (fun t ht => h t (by simp [ht])))

theorem prime_divisor_odd {S : Finset ℕ} (D : PrimeEnumeration S)
    (hS : ∀ p ∈ S, 2<p ∧ p.Prime) {d : ℕ} (hd : d ∣ D.ps.prod) : Odd d := by
  have ho := odd_product_list D.ps (fun p hp => by
    obtain ⟨h2,hpr⟩ := hS p ((D.mem p).mp hp)
    exact hpr.odd_of_ne_two (by omega))
  apply Nat.odd_iff.mpr
  by_contra he
  have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
  exact ho.not_two_dvd_nat (h2.trans hd)

theorem prime_divisor_coprime {S : Finset ℕ} (D : PrimeEnumeration S)
    (hS : ∀ p ∈ S, 2<p ∧ p.Prime) {p : ℕ} (hp : p.Prime) (hne : p∉S)
    {d : ℕ} (hd : d ∣ D.ps.prod) : d.Coprime (p^2) := by
  have hc := cop_product_list D.ps p (fun q hq => by
    have hqm := (D.mem q).mp hq
    exact (Nat.coprime_primes (hS q hqm).2 hp).mpr (by rintro rfl; exact hne hqm))
  exact (hc.coprime_dvd_left hd).pow_right 2

def initialError (r : ℕ) : ℚ := if r=0 then 0 else (2:ℚ)^(r-1)

theorem initial_candidates {S : Finset ℕ} (D : PrimeEnumeration S) (b J : ℕ)
    (hS : ∀ p ∈ S, 2<p ∧ p.Prime) (hb : b=1 ∨ b=2) :
    (J:ℚ)*largeRho S - initialError S.card ≤ ((candidateSet D.ps J b).card:ℚ) := by
  classical
  have hp : ∀ p ∈ D.ps, p.Prime := fun p hm => (hS p ((D.mem p).mp hm)).2
  have hd : ∀ d : ℕ, d ∣ D.ps.prod → Odd d := fun _ he => prime_divisor_odd D hS he
  by_cases he : D.ps=[]
  · have hsc : S.card=0 := by simpa only [←D.len,he,List.length_nil]
    have hr : largeRho S=1 := by rw [←D.rho,he]; simp [density]
    simp [candidateSet,he,hsc,hr,initialError]
  · have hlen : 0<D.ps.length := by
      cases h : D.ps with
      | nil => exact False.elim (he h)
      | cons p ps => simp
    have hspos : 0<S.card := by rw [← D.len]; exact hlen
    have hhalf : (2:ℚ)^D.ps.length/2 = initialError S.card := by
      rw [D.len,initialError,if_neg (by omega)]
      conv_lhs => rw [show S.card=S.card-1+1 by omega,pow_succ]
      ring
    have hh : |((candidateSet D.ps J b).card:ℚ) - (J:ℚ)*largeRho S|
        ≤ initialError S.card := by
      rcases hb with rfl | rfl
      · have hh := initial_odd_coprime D.ps D.pair hp hd J
        simpa only [Finset.sum_boole,D.rho,hhalf,candidateSet] using hh
      · have hh := initial_even_coprime D.ps he D.pair hp hd J
        simpa only [Finset.sum_boole,D.rho,hhalf,candidateSet] using hh
    have := (abs_le.mp hh).1
    linarith

theorem cover_candidates {S : Finset ℕ} (D : PrimeEnumeration S) {n b J : ℕ}
    (hreg : ∀ p : ℕ, 2<p → p.Prime → (p∈S ↔ p^2 ∣ n))
    (hb : b=1 ∨ b=2) (hfit : ∀ x<J, (2*x+b)^2<n)
    (hupper : (n-1).sqrt ≤ 2*J+1) (hpar : ∀ x<J, ¬4 ∣ n-(2*x+b)^2)
    (hnone : ¬ ∃ x<J, Squarefree (n-(2*x+b)^2)) :
    candidateSet D.ps J b ⊆ ((largePrimeSet (2*J+1)) \ S).biUnion
      (fun p => hitSet n p D.ps J b) := by
  classical
  intro x hx
  obtain ⟨hr,hc⟩ := Finset.mem_filter.mp hx
  have hlt := Finset.mem_range.mp hr
  have hsq := hfit x hlt
  have hbad : ¬Squarefree (n-(2*x+b)^2) := fun hh => hnone ⟨x,hlt,hh⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hbad
  push_neg at hbad
  obtain ⟨p,hp,hpd⟩ := hbad
  have hd : p^2 ∣ n-(2*x+b)^2 := by simpa only [pow_two] using hpd
  have h2 : 2<p := by
    have := hp.two_le
    by_contra! hh
    have he : p=2 := by omega
    exact hpar x hlt (by simpa [he] using hpd)
  have hnmem : p∉S := by
    intro hpS
    have hpn := (hreg p h2 hp).mp hpS
    have hdiff := Nat.dvd_sub hpn hd
    have hback : n-(n-(2*x+b)^2)=(2*x+b)^2 := by omega
    rw [hback] at hdiff
    have hpk : p ∣ 2*x+b := by
      have hh : p ∣ (2*x+b)*(2*x+b) :=
        (Nat.dvd_mul_right p p).trans (by simpa only [pow_two] using hdiff)
      exact (hp.dvd_mul.mp hh).elim id id
    have hbprod : p ∣ D.ps.prod := by rw [D.product]; exact Finset.dvd_prod_of_mem id hpS
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hbprod hpk hc
  have ple := Nat.le_of_dvd (show 0<n-(2*x+b)^2 by omega) hd
  have hroot : p ≤ (n-1).sqrt := Nat.le_sqrt'.mpr (by
    have hk : 0<2*x+b := by rcases hb with rfl | rfl <;> omega
    have := pow_pos hk 2
    omega)
  have hpmem : p∈largePrimeSet (2*J+1) := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega),h2,hp⟩
  exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hpmem,hnmem⟩,
    Finset.mem_filter.mpr ⟨hx,Nat.modEq_of_dvd' hsq.le hd⟩⟩

end A085265InclusionExclusion

namespace A085265Sieve

private theorem odd_reciprocal_step {p T : ℕ} (hT : 1 ≤ T) (hTp : T < p) :
    1/(p : ℚ)^2 + 1/(2*((p : ℚ)+1)) ≤ 1/(2*(T : ℚ)) := by
  have hpos : (0 : ℚ) < T := by exact_mod_cast (show 0 < T by omega)
  have hle : (T : ℚ)+1 ≤ p := by exact_mod_cast (show T+1 ≤ p by omega)
  have hm : 0 < (p : ℚ)-1 := by linarith
  have hp : 0 < (p : ℚ)+1 := by positivity
  have htel : 1/(2*((p : ℚ)-1)) - 1/(2*((p : ℚ)+1)) =
      1/(((p : ℚ)-1)*((p : ℚ)+1)) := by
    field_simp [hm.ne', hp.ne'] <;> ring
  have hrec : 1/(p : ℚ)^2 ≤ 1/(((p : ℚ)-1)*((p : ℚ)+1)) :=
    one_div_le_one_div_of_le (mul_pos hm hp) (by nlinarith)
  have hstart : 1/(2*((p : ℚ)-1)) ≤ 1/(2*(T : ℚ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

private theorem odd_reciprocal_tail_aux (count : ℕ) (P : Finset ℕ)
    (hcard : P.card = count) (T : ℕ) (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) := by
  induction count generalizing P T with
  | zero =>
    have he := Finset.card_eq_zero.mp hcard
    subst P
    simp only [Finset.sum_empty]
    positivity
  | succ count ih =>
    have hne : P.Nonempty := Finset.card_pos.mp (by omega)
    let p := P.min' hne
    have hp : p ∈ P := P.min'_mem hne
    have hcard' : (P.erase p).card = count := by
      rw [Finset.card_erase_of_mem hp, hcard] <;> omega
    have hsub {q : ℕ} (hq : q ∈ P.erase p) : q ∈ P := (Finset.mem_erase.mp hq).2
    have hnext (q : ℕ) (hq : q ∈ P.erase p) : p+1 < q := by
      have hdiff := (Finset.mem_erase.mp hq).1
      have hmin : p ≤ q := P.min'_le q (hsub hq)
      obtain ⟨hp2,hpp⟩ := hP p hp
      obtain ⟨hq2,hqp⟩ := hP q (hsub hq)
      obtain ⟨i,hi⟩ := hpp.odd_of_ne_two (by omega)
      obtain ⟨j,hj⟩ := hqp.odd_of_ne_two (by omega)
      omega
    have htail := ih (P.erase p) hcard' (p+1) (by omega)
      (fun q hq => hP q (hsub hq)) hnext
    simp only [Nat.cast_add, Nat.cast_one] at htail
    have hsum := add_le_add (le_refl (1 / (p : ℚ)^2)) htail
    rw [← Finset.add_sum_erase P (fun q => 1/(q : ℚ)^2) hp]
    exact hsum.trans (odd_reciprocal_step hT (hcut p hp))

/-- A finite subset of the odd primes past `T` has reciprocal-square sum at
most `1/(2T)`, by telescoping along successive odd integers. -/
theorem oddPrimeReciprocalTail {P : Finset ℕ} {T : ℕ} (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) :=
  odd_reciprocal_tail_aux P.card P rfl T hT hP hcut

private def initialOddPrimes : Finset ℕ :=
  (Finset.range 39).filter (fun p => 2 < p ∧ p.Prime)

private theorem initial_reciprocal_sum :
    (∑ p ∈ initialOddPrimes, 1/(p : ℚ)^2) + 1/76 ≤ 21/100 := by decide +kernel

private theorem odd_reciprocal_sum_aux {P : Finset ℕ} (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 21/100 := by
  let small := P.filter (fun p => p ≤ 38)
  let large := P.filter (fun p => ¬p ≤ 38)
  have hsub : small ⊆ initialOddPrimes := by
    intro p hp
    obtain ⟨hmem,hle⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP p hmem⟩
  have hsmall : (∑ p ∈ small, 1/(p : ℚ)^2) ≤ ∑ p ∈ initialOddPrimes, 1/(p : ℚ)^2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have hlarge := oddPrimeReciprocalTail (P := large) (T := 38) (by decide)
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
    (fun p hp => by
      have hgt := (Finset.mem_filter.mp hp).2
      omega)
  have hs : (∑ p ∈ small, 1/(p : ℚ)^2) + (∑ p ∈ large, 1/(p : ℚ)^2) =
      ∑ p ∈ P, 1/(p : ℚ)^2 :=
    Finset.sum_filter_add_sum_filter_not P (fun p => p ≤ 38) (fun p => 1/(p : ℚ)^2)
  calc
    _ = _ := hs.symm
    _ ≤ _ := add_le_add hsmall hlarge
    _ ≤ _ := by convert initial_reciprocal_sum using 1 <;> norm_num

/-- The global odd-prime bound, credited back for three when disjointness
excludes that prime from the sum. -/
theorem oddPrimeReciprocalSum {P S : Finset ℕ} (hP : ∀ p ∈ P, 2 < p ∧ p.Prime)
    (hdis : Disjoint P S) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 21/100 - (if 3 ∈ S then 1/9 else 0) := by
  by_cases h3 : 3 ∈ S
  · have hout : 3 ∉ P := fun hp => Finset.disjoint_left.mp hdis hp h3
    have hsum := odd_reciprocal_sum_aux (P := insert 3 P) (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hmem
      · decide
      · exact hP p hmem)
    rw [Finset.sum_insert hout] at hsum
    rw [if_pos h3]
    norm_num at hsum ⊢ <;> linarith
  · simpa [h3] using odd_reciprocal_sum_aux hP

end A085265Sieve

namespace A085265Moderate

open A085265InclusionExclusion

/-- Legendre's finite sieve with a cutoff when the divisor exceeds the interval. -/
def fastSift (ps : List ℕ) (x d : ℕ) : ℤ :=
  match ps with
  | [] => ((x/d : ℕ) : ℤ)
  | p::rest => if x < d then 0 else fastSift rest x d - fastSift rest x (d*p)

private theorem sift_empty_interval (ps : List ℕ) (x d : ℕ) (h : x < d)
    (hp : ∀ p ∈ ps, 0 < p) : sift ps (fun t => ((x/t : ℕ) : ℚ)) d = 0 := by
  induction ps generalizing d with
  | nil => simp [sift, Nat.div_eq_of_lt h]
  | cons p rest ih =>
    have hrest : ∀ q ∈ rest, 0 < q := fun q hq => hp q (by simp [hq])
    have hp1 := hp p (by simp)
    have hmul : d ≤ d*p := by simpa using Nat.mul_le_mul_left d hp1
    rw [sift,ih d h hrest,ih (d*p) (h.trans_le hmul) hrest,sub_zero]

theorem fastSift_cast (ps : List ℕ) (x d : ℕ) (hp : ∀ p ∈ ps, 0 < p) :
    (fastSift ps x d : ℚ) = sift ps (fun t => ((x/t : ℕ):ℚ)) d := by
  induction ps generalizing d with
  | nil => simp only [fastSift, sift, Int.cast_natCast]
  | cons p rest ih =>
    have hrest : ∀ q ∈ rest, 0 < q := fun q hq => hp q (by simp [hq])
    by_cases h : x < d
    · simp [fastSift,h,sift_empty_interval (p::rest) x d h hp]
    · simp [fastSift,sift,h,ih d hrest,ih (d*p) hrest]

theorem rough_card (ps : List ℕ) (x : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hpair : ps.Pairwise Nat.Coprime) :
    (((Finset.Ioc 0 x).filter (fun k => ps.prod.Coprime k)).card : ℤ) = fastSift ps x 1 := by
  have counts (d : ℕ) : ((x/d : ℕ):ℚ) = ∑ k ∈ Finset.Ioc 0 x, if d ∣ k then (1:ℚ) else 0 := by
    rw [Finset.sum_boole, Nat.Ioc_filter_dvd_card_eq_div]
  have h : (fastSift ps x 1 : ℚ) =
      (((Finset.Ioc 0 x).filter (fun k => ps.prod.Coprime k)).card : ℚ) := by
    rw [fastSift_cast ps x 1 (fun p h => (hp p h).pos)]
    simp only [counts,sift_sum]
    simp only [sift_indicator ps _ 1 hpair hp (fun p _ => Nat.coprime_one_left p),
      one_dvd,true_and,Finset.sum_boole]
  exact_mod_cast h.symm

def wheel : List ℕ :=
  [101,97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2]

set_option maxRecDepth 20000 in
private theorem wheel_complete : ∀ p : Fin 102, 2 < p.val → Nat.Prime p.val →
    p.val ∈ wheel.toFinset.erase 2 := by decide +kernel

theorem odd_prime_count_upper (x : ℕ) (hx : 101 ≤ x) :
    ((((Finset.range (x+1)).filter (fun p => 2 < p ∧ p.Prime)).card : ℤ)) ≤
      fastSift wheel x 1 + 24 := by
  let rough := (Finset.Ioc 0 x).filter (fun k => wheel.prod.Coprime k)
  let known := wheel.toFinset.erase 2
  have facts : ∀ p ∈ wheel, Nat.Prime p ∧ p ≤ 101 := by decide
  have hp : ∀ p ∈ wheel, Nat.Prime p := fun _ h => (facts _ h).1
  have hknown : known.card = 25 := by decide
  have hone : 1 ∈ rough := by simp [rough,Finset.mem_Ioc] <;> omega
  have hsub : (Finset.range (x+1)).filter (fun p => 2 < p ∧ p.Prime) ⊆
      known ∪ rough.erase 1 := by
    intro p h
    obtain ⟨hx',h₂,hp'⟩ := Finset.mem_filter.mp h
    have hpx := Finset.mem_range.mp hx'
    by_cases hsmall : p ≤ 101
    · exact Finset.mem_union_left _ (wheel_complete ⟨p,by omega⟩ h₂ hp')
    · apply Finset.mem_union_right
      apply Finset.mem_erase.mpr
      refine ⟨by omega,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,?_⟩⟩
      apply Nat.coprime_list_prod_left_iff.mpr
      intro q hq
      apply Nat.Coprime.symm
      apply hp'.coprime_iff_not_dvd.mpr
      intro hdiv
      have := Nat.le_of_dvd (hp q hq).pos hdiv
      have := (facts q hq).2
      omega
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hknown,Finset.card_erase_of_mem hone] at hc
  have hp1 := Finset.card_pos.mpr ⟨1,hone⟩
  have hval : (rough.card : ℤ) = fastSift wheel x 1 :=
    rough_card wheel x hp (by decide)
  omega

def primeDeltas (j : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range 1415).filter (fun p => 2 < p ∧ p.Prime), 2*j/(p^2)

def costUpper (j : ℕ) : ℤ := fastSift wheel (2*j+1) 1 + 24 + primeDeltas j

theorem cost_upper (j : ℕ) (hlo : 300 ≤ j) (hhi : j ≤ 1000000) :
    ((∑ p ∈ (Finset.range (2*j+2)).filter (fun p => 2 < p ∧ p.Prime),
      ((2*j)/(p^2)+1) : ℕ):ℤ) ≤ costUpper j := by
  let P := (Finset.range (2*j+2)).filter (fun p => 2 < p ∧ p.Prime)
  let Q := (Finset.range 1415).filter (fun p => 2 < p ∧ p.Prime)
  have outside (p : ℕ) (hp : p ∈ P \ Q) : 2*j/(p^2) = 0 := by
    obtain ⟨hmem,hn⟩ := Finset.mem_sdiff.mp hp
    have hpp := (Finset.mem_filter.mp hmem).2
    have hbig : 1415 ≤ p := by
      by_contra! h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h,hpp⟩)
    apply Nat.div_eq_of_lt
    have hp2 := Nat.pow_le_pow_left hbig 2
    omega
  have hfloor : (∑ p ∈ P, 2*j/(p^2)) ≤ primeDeltas j := by
    have remove : (∑ p ∈ P \ Q, 2*j/(p^2)) = 0 := Finset.sum_eq_zero outside
    have add := Finset.sum_sdiff (f := fun p => 2*j/(p^2))
      (show P ∩ Q ⊆ P from Finset.inter_subset_left)
    have eq : P \ (P ∩ Q) = P \ Q := by ext p; simp <;> tauto
    rw [eq, remove, zero_add] at add
    rw [← add]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    exact fun _ _ _ => Nat.zero_le _
  have hcard := odd_prime_count_upper (2*j+1) (by omega)
  change (P.card : ℤ) ≤ _ at hcard
  change ((∑ p ∈ P, (2*j/(p^2)+1) : ℕ):ℤ) ≤ _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_add]
  unfold costUpper
  omega

end A085265Moderate

namespace A085265Moderate

def rows : List (ℕ × ℕ × ℤ) := [
  (300, 307, 227),
  (308, 314, 231),
  (315, 323, 238),
  (324, 332, 244),
  (333, 341, 251),
  (342, 355, 259),
  (356, 368, 269),
  (369, 385, 280),
  (386, 409, 293),
  (410, 430, 312),
  (431, 454, 327),
  (455, 484, 347),
  (485, 517, 371),
  (518, 550, 396),
  (551, 592, 422),
  (593, 643, 454),
  (644, 710, 494),
  (711, 782, 546),
  (783, 865, 605),
  (866, 964, 669),
  (965, 1082, 747),
  (1083, 1228, 842),
  (1229, 1400, 957),
  (1401, 1624, 1093),
  (1625, 1885, 1268),
  (1886, 2213, 1477),
  (2214, 2501, 1658),
  (2502, 2810, 1852),
  (2811, 3175, 2085),
  (3176, 3613, 2359),
  (3614, 4153, 2693),
  (4154, 4805, 3100),
  (4806, 5602, 3595),
  (5603, 6574, 4198),
  (6575, 7745, 4933),
  (7746, 9163, 5819),
  (9164, 10868, 6888),
  (10869, 12905, 8173),
  (12906, 15340, 9709),
  (15341, 18230, 11541),
  (18231, 21628, 13710),
  (21629, 25645, 16264),
  (25646, 30356, 19280),
  (30357, 35902, 22818),
  (35903, 42385, 26976),
  (42386, 47546, 30284),
  (47547, 53065, 33821),
  (53066, 59170, 37742),
  (59171, 65906, 42074),
  (65907, 73363, 46859),
  (73364, 81562, 52146),
  (81563, 90625, 57967),
  (90626, 100606, 64397),
  (100607, 111608, 71479),
  (111609, 123731, 79287),
  (123732, 137092, 87888),
  (137093, 151816, 97368),
  (151817, 168016, 107812),
  (168017, 185867, 119305),
  (185868, 205514, 131967),
  (205515, 227137, 145904),
  (227138, 250933, 161241),
  (250934, 277159, 178125),
  (277160, 306017, 196728),
  (306018, 337817, 217203),
  (337818, 372854, 239765),
  (372855, 411418, 264618),
  (411419, 453940, 291986),
  (453941, 500809, 322156),
  (500810, 552482, 355415),
  (552483, 609460, 392084),
  (609461, 672335, 432525),
  (672336, 741674, 477145),
  (741675, 808306, 519980),
  (808307, 851143, 547552),
  (851144, 896314, 576584),
  (896315, 936791, 602620),
  (936792, 979100, 629835),
  (979101, 1000000, 643264)]

end A085265Moderate

namespace A085265Moderate

open A085265Sieve

private def smallPrimes : Finset ℕ := {3,5,7,11,13,17}

private def initialError (r : ℕ) : ℚ := if r = 0 then 0 else (2:ℚ)^(r-1)

private def refund (J : ℕ) (A : Finset ℕ) : ℕ := ∑ p ∈ A, (2*J/(p^2)+1)

private def profileChecks (lo hi : ℕ) (c : ℤ) : Prop :=
  ∀ A ∈ smallPrimes.powerset, ∀ t : Fin 5,
    (∏ p ∈ A,p)*19^t.val ≤ 2*hi+2 →
      (c:ℚ) - (refund hi A:ℚ) + initialError (A.card+t.val) <
        (lo:ℚ)*largeRho A*(18/19:ℚ)^t.val

private def covers (fromN : ℕ) : List (ℕ × ℕ × ℤ) → Prop
  | [] => 1000000 < fromN
  | row::rest => row.1 ≤ fromN ∧ fromN ≤ row.2.1+1 ∧ covers (row.2.1+1) rest

private instance coversDec (k : ℕ) (cs : List (ℕ × ℕ × ℤ)) : Decidable (covers k cs) := by
  induction cs generalizing k with
  | nil => exact inferInstanceAs (Decidable (1000000 < k))
  | cons c tail ih =>
    unfold covers
    letI := ih (c.2.1+1)
    infer_instance

private theorem covers_mem {k J : ℕ} {cs : List (ℕ × ℕ × ℤ)} (hk : k ≤ J)
    (hj : J ≤ 1000000) (hc : covers k cs) : ∃ c ∈ cs, c.1 ≤ J ∧ J ≤ c.2.1 := by
  induction cs generalizing k with
  | nil => change 1000000 < k at hc; omega
  | cons c cs ih =>
    obtain ⟨hstart,hend,ht⟩ := hc
    by_cases h : J ≤ c.2.1
    · exact ⟨c,by simp,hstart.trans hk,h⟩
    · obtain ⟨row,hr,hl,hu⟩ := ih (by omega : c.2.1+1 ≤ J) ht
      exact ⟨row,by simp [hr],hl,hu⟩

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
private theorem checks : ∀ c ∈ rows, 300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧
    profileChecks c.1 c.2.1 c.2.2 ∧ costUpper c.2.1 ≤ c.2.2 := by
  unfold profileChecks
  decide +kernel

private theorem rho_nonneg' {S : Finset ℕ} (h : ∀ p ∈ S, 2 < p) : 0 ≤ largeRho S := by
  apply Finset.prod_nonneg
  intro p hp
  have h₁ : (1:ℚ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := h p hp; omega)
  exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℚ) < p)).mpr h₁)

private theorem missing_mono {J H : ℕ} (hj : J ≤ H) {S A : Finset ℕ} (ha : A ⊆ S) :
    (∑ p ∈ largePrimeSet (2*J+1) \ S, (2*J/(p^2)+1)) ≤
      ∑ p ∈ largePrimeSet (2*H+1) \ A, (2*H/(p^2)+1) := by
  have sub : largePrimeSet (2*J+1) \ S ⊆ largePrimeSet (2*H+1) \ A := by
    intro p hp
    obtain ⟨hP,hs⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hR,hp⟩ := Finset.mem_filter.mp hP
    have hx := Finset.mem_range.mp hR
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩,
      fun hp => hs (ha hp)⟩
  calc
    _ ≤ ∑ p ∈ largePrimeSet (2*J+1) \ S, (2*H/(p^2)+1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hj)) 1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)

set_option maxHeartbeats 2000000 in
theorem moderate_sieve_budget {J : ℕ} (hlo : 300 ≤ J) (hhi : J ≤ 1000000)
    {S : Finset ℕ} (hS : ∀ p ∈ S, 2 < p ∧ p.Prime) (hB : (∏ p ∈ S,p) ≤ 2*J+2) :
    ((∑ p ∈ largePrimeSet (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
        (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) < (J:ℚ)*largeRho S := by
  obtain ⟨c,hc,hl,hu⟩ := covers_mem hlo hhi (show covers 300 rows by decide)
  obtain ⟨hl₀,hu₀,hcases,hcost⟩ := checks c hc
  let A := S ∩ smallPrimes
  let T := S \ A
  have haS : A ⊆ S := Finset.inter_subset_left
  have hat : Disjoint A T := Finset.disjoint_left.mpr
    (fun _ ha ht => (Finset.mem_sdiff.mp ht).2 ha)
  have hsplit : A ∪ T = S := Finset.union_sdiff_of_subset haS
  have card : A.card+T.card = S.card := by rw [← Finset.card_union_of_disjoint hat,hsplit]
  have large (p : ℕ) (hp : p ∈ T) : 19 ≤ p := by
    obtain ⟨hs,ha⟩ := Finset.mem_sdiff.mp hp
    have tab : ∀ t : Fin 19, 2 < t.val → Nat.Prime t.val → t.val ∈ smallPrimes := by decide
    by_contra! h
    have prop := hS p hs
    exact ha (Finset.mem_inter.mpr ⟨hs,tab ⟨p,h⟩ prop.1 prop.2⟩)
  have pT : 19^T.card ≤ ∏ p ∈ T,p := by
    simpa only [Finset.prod_const] using (Finset.prod_le_prod' (fun p hp => large p hp))
  have pA : (∏ p ∈ A,p)*19^T.card ≤ 2*J+2 := calc
    _ ≤ _ := Nat.mul_le_mul_left (∏ p ∈ A,p) pT
    _ = ∏ p ∈ S,p := by rw [← Finset.prod_union hat,hsplit]
    _ ≤ _ := hB
  have pApos : 0 < ∏ p ∈ A,p := Finset.prod_pos (fun p hp => by have := (hS p (haS hp)).1; omega)
  have pTle : 19^T.card ≤ 2*J+2 := (Nat.le_mul_of_pos_left _ pApos).trans pA
  have ht : T.card < 5 := by
    by_contra! hk
    have high := Nat.pow_le_pow_right (by decide : 0 < 19) hk
    omega
  have hcase := hcases A (Finset.mem_powerset.mpr Finset.inter_subset_right) ⟨T.card,ht⟩
      (pA.trans (by omega))
  have hTρ : (18/19:ℚ)^T.card ≤ largeRho T := by
    have point (p : ℕ) (hp : p ∈ T) : (18/19:ℚ) ≤ 1-1/(p:ℚ) := by
      have pq : (19:ℚ) ≤ p := by exact_mod_cast large p hp
      have inf := one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 19) pq
      linarith
    have bound (U : Finset ℕ) (hu : ∀ p ∈ U, (18/19:ℚ) ≤ 1-1/(p:ℚ)) :
        (18/19:ℚ)^U.card ≤ largeRho U := by
      induction U using Finset.induction_on with
      | empty => simp [largeRho]
      | @insert p U hp ih =>
        have hp' := hu p (Finset.mem_insert_self p U)
        have hi := ih (fun q hq => hu q (Finset.mem_insert_of_mem hq))
        have h := mul_le_mul hp' hi (by positivity)
          (by linarith only [hp'] : 0 ≤ 1-1/(p:ℚ))
        simpa [largeRho, hp, pow_succ, mul_comm] using h
    exact bound T point
  have hρA := rho_nonneg' (S := A) (fun p hp => (hS p (haS hp)).1)
  have hrho : largeRho A * largeRho T = largeRho S := by
    unfold largeRho
    rw [← Finset.prod_union hat,hsplit]
  have hright : (c.1:ℚ)*largeRho A*(18/19:ℚ)^T.card ≤ (J:ℚ)*largeRho S := calc
    _ = (c.1:ℚ)*(largeRho A*(18/19:ℚ)^T.card) := by ring
    _ ≤ (c.1:ℚ)*(largeRho A*largeRho T) := by gcongr
    _ = _ := by rw [hrho]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hl) (rho_nonneg' (fun p hp => (hS p hp).1))
  have hA : A ⊆ largePrimeSet (2*c.2.1+1) := by
    intro p hp
    have props := hS p (haS hp)
    have tab : ∀ q ∈ smallPrimes, q ≤ 17 := by decide
    have hle := tab p (Finset.mem_inter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),props⟩
  have hrebate := Finset.sum_sdiff (f := fun p => 2*c.2.1/(p^2)+1) hA
  have htotal := (cost_upper c.2.1 (hl₀.trans (hl.trans hu)) hu₀).trans hcost
  have hmono := missing_mono hu haS
  have hleft : ((∑ p ∈ largePrimeSet (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) ≤
      (c.2.2:ℚ) - (refund c.2.1 A:ℚ) := by
    apply le_sub_iff_add_le.mpr
    have hsum := (Nat.add_le_add_right hmono (refund c.2.1 A)).trans_eq hrebate
    have hsumZ : (((∑ p ∈ largePrimeSet (2*J+1) \ S, (2*J/(p^2)+1)) +
        refund c.2.1 A : ℕ) : ℤ) ≤ c.2.2 := calc
      _ ≤ ((∑ p ∈ largePrimeSet (2*c.2.1+1), (2*c.2.1/(p^2)+1) : ℕ) : ℤ) := by
        exact_mod_cast hsum
      _ ≤ _ := htotal
    exact_mod_cast hsumZ
  change _ + initialError S.card < _
  rw [← card]
  exact (add_le_add hleft le_rfl).trans_lt (hcase.trans_le hright)

end A085265Moderate

namespace A085265InclusionExclusion

open A085265Sieve A085265Moderate

private theorem error_le_pow (r : ℕ) : initialError r ≤ (2:ℚ)^r := by
  cases r with
  | zero => norm_num [initialError]
  | succ r =>
    simp only [initialError, Nat.succ_ne_zero, if_false, Nat.add_one_sub_one, pow_succ]
    have : 0 ≤ (2:ℚ)^r := by positivity
    linarith

private theorem nat_divide_cost (J p : ℕ) (hp : 0<p) :
    ((2*J/(p^2)+1:ℕ):ℚ) ≤ 2*(J:ℚ)*(1/(p:ℚ)^2)+1 := by
  have hmul := Nat.div_mul_le_self (2*J) (p^2)
  have hq : ((2*J/(p^2):ℕ):ℚ)*(p:ℚ)^2 ≤ 2*(J:ℚ) := by exact_mod_cast hmul
  have hd : (0:ℚ)<(p:ℚ)^2 := by positivity
  have := (le_div_iff₀ hd).mpr hq
  push_cast
  simpa only [div_eq_mul_inv,one_mul] using add_le_add this (le_refl (1:ℚ))

/-- Estimate the union of bad prime-square divisors on the retained parity progression. -/
private theorem large_hit_total {n J b T : ℕ} {S : Finset ℕ} (D : PrimeEnumeration S)
    (hT : 1≤T) (hS : ∀ p ∈ S, 2<p ∧ p.Prime)
    (hreg : ∀ p : ℕ, 2<p → p.Prime → (p∈S ↔ p^2 ∣ n)) (hb : b≤2) :
    (∑ p ∈ (largePrimeSet (2*J+1)) \ S, ((hitSet n p D.ps J b).card:ℚ)) ≤
      2*(J:ℚ)*(largeRho S)*(21/100 - if 3∈S then 1/9 else 0)
      + (largePi (2*J+1):ℚ) + 2*(2:ℚ)^S.card*(largePi T:ℚ) + (J:ℚ)/T := by
  classical
  let P := (largePrimeSet (2*J+1)) \ S
  let lo := P.filter (fun p => p≤T)
  let hi := P.filter (fun p => T<p)
  let w (p : ℕ) : ℚ := 1/(p:ℚ)^2
  let K := 2*(J:ℚ)*largeRho S
  let E := (2:ℚ)^S.card
  have rho : 0 ≤ largeRho S := by
    apply Finset.prod_nonneg
    intro p hp
    have hnat : 1 ≤ p := by have := (hS p hp).1; omega
    have hq : (1:ℚ) ≤ p := by exact_mod_cast hnat
    exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℚ)<p)).mpr hq)
  have kpos : 0 ≤ K := by dsimp [K]; positivity
  have epos : 0 ≤ E := by dsimp [E]; positivity
  have hP {p : ℕ} (hp : p∈P) : 2<p ∧ p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
  have notsq {p : ℕ} (hp : p∈P) : ¬p^2 ∣ n :=
    fun hd => (Finset.mem_sdiff.mp hp).2 ((hreg p (hP hp).1 (hP hp).2).mpr hd)
  have hterm (p : ℕ) (hp : p∈P) :
      ((hitSet n p D.ps J b).card:ℚ) ≤ (K*w p + 1) +
        (if p≤T then 2*E else 0) + (if T<p then 2*(J:ℚ)*w p else 0) := by
    obtain ⟨h2,hpr⟩ := hP hp
    by_cases hsmall : p≤T
    · have hl := hit_card_sifted D.ps J b hpr h2 (notsq hp) D.pair
        (fun q hq => (hS q ((D.mem q).mp hq)).2) (by rwa [D.rho])
        (fun d hd => ⟨prime_divisor_coprime D hS hpr (Finset.mem_sdiff.mp hp).2 hd,
          (prime_divisor_odd D hS hd).mul (hpr.odd_of_ne_two (by omega)).pow⟩)
      rw [D.rho,D.len] at hl
      simp only [hsmall,if_true,not_lt.mpr hsmall,if_false,add_zero,K,w,E]
      simp only [div_eq_mul_inv,one_mul] at hl ⊢
      linarith
    · have hraw : ((hitSet n p D.ps J b).card:ℚ) ≤ ((2*J/(p^2)+1:ℕ):ℚ) := by
        exact_mod_cast hit_card_raw D.ps hpr h2 (notsq hp) hb
      have hl := hraw.trans (nat_divide_cost J p hpr.pos)
      have hk : 0 ≤ K*w p := mul_nonneg kpos (by dsimp [w]; positivity)
      change ((hitSet n p D.ps J b).card:ℚ) ≤ 2*(J:ℚ)*w p+1 at hl
      simp only [hsmall,if_false,lt_of_not_ge hsmall,if_true,add_zero]
      linarith
  have hsumLo : (∑ p ∈ P, if p≤T then 2*E else 0) = (lo.card:ℚ)*(2*E) := by
    rw [← Finset.sum_filter]
    simp [lo, nsmul_eq_mul]
  have hsumHi : (∑ p ∈ P, if T<p then 2*(J:ℚ)*w p else 0)
      = 2*(J:ℚ)* ∑ p ∈ hi, w p := by rw [← Finset.sum_filter,Finset.mul_sum]
  have sumAll : (∑ p ∈ P, ((hitSet n p D.ps J b).card:ℚ)) ≤
      K*(∑ p ∈ P, w p) + (P.card:ℚ) + (lo.card:ℚ)*(2*E) + 2*(J:ℚ)*(∑ p ∈ hi,w p) := by
    have hh := Finset.sum_le_sum hterm
    simpa only [Finset.sum_add_distrib, ←Finset.mul_sum,hsumLo,hsumHi,
      Finset.sum_const, nsmul_eq_mul, mul_one] using hh
  have hcnt : P.card ≤ largePi (2*J+1) := Finset.card_le_card Finset.sdiff_subset
  have hlcnt : lo.card ≤ largePi T := by
    apply Finset.card_le_card
    intro p hm
    obtain ⟨hp,hpt⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hP hp⟩
  have hd : Disjoint P S := Finset.disjoint_left.mpr (fun _ hp hs => (Finset.mem_sdiff.mp hp).2 hs)
  have hw := oddPrimeReciprocalSum (P:=P) (S:=S) (fun _ hp => hP hp) hd
  have ht := oddPrimeReciprocalTail (P:=hi) (T:=T) hT
    (fun _ hp => hP (Finset.mem_filter.mp hp).1) (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hq : (0:ℚ)<T := by exact_mod_cast (show 0<T by omega)
  have tail : (2*(J:ℚ))*(∑ p ∈ hi,w p) ≤ (J:ℚ)/T := by
    calc
      _ ≤ (2*(J:ℚ))*(1/(2*(T:ℚ))) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by field_simp [ne_of_gt hq] <;> ring
  have main := mul_le_mul_of_nonneg_left hw kpos
  have c1 : (P.card:ℚ) ≤ (largePi (2*J+1):ℚ) := by exact_mod_cast hcnt
  have c2 : (lo.card:ℚ) ≤ (largePi T:ℚ) := by exact_mod_cast hlcnt
  have c3 := mul_le_mul_of_nonneg_right c2 (show 0 ≤ 2*E by positivity)
  change (∑ p ∈ P, ((hitSet n p D.ps J b).card:ℚ)) ≤
    K*(21/100 - if 3∈S then 1/9 else 0) + (largePi (2*J+1):ℚ)
      + 2*E*(largePi T:ℚ) + (J:ℚ)/T
  change K*(∑ p ∈ P,w p) ≤ _ at main
  linarith

theorem large_or_moderate_rep {n J b : ℕ} (S : Finset ℕ) (hJ : 300 ≤ J)
    (hb : b=1 ∨ b=2) (hS : ∀ p ∈ S, 2<p ∧ p.Prime)
    (hreg : ∀ p : ℕ, 2<p → p.Prime → (p∈S ↔ p^2∣n))
    (hB : (∏ p ∈ S,p) ≤ 2*J+2) (hfit : ∀ x<J, (2*x+b)^2<n)
    (hupper : (n-1).sqrt ≤ 2*J+1) (hpar : ∀ x<J, ¬4∣n-(2*x+b)^2) :
    ∃ x<J, Squarefree (n-(2*x+b)^2) := by
  classical
  obtain ⟨D⟩ := prime_enumeration S hS
  have hb2 : b≤2 := by rcases hb with rfl | rfl <;> omega
  by_contra hnone
  let P := (largePrimeSet (2*J+1)) \ S
  have cover := cover_candidates D hreg hb hfit hupper hpar hnone
  have hc : (candidateSet D.ps J b).card ≤ ∑ p ∈ P, (hitSet n p D.ps J b).card :=
    (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have initial := initial_candidates D b J hS hb
  by_cases hm : J ≤ 1000000
  · have budget := moderate_sieve_budget (S:=S) hJ hm hS hB
    have hh : (candidateSet D.ps J b).card ≤ ∑ p ∈ P, (2*J/(p^2)+1) := by
      refine hc.trans ?_
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hh,hno⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨h2,hpr⟩ := (Finset.mem_filter.mp hh).2
      exact hit_card_raw D.ps hpr h2 (fun h => hno ((hreg p h2 hpr).mpr h)) hb2
    have hcast : ((candidateSet D.ps J b).card:ℚ) ≤ ((∑ p ∈ P, (2*J/(p^2)+1) : ℕ):ℚ) := by
      exact_mod_cast hh
    change ((∑ p ∈ P, (2*J/(p^2)+1) : ℕ):ℚ) + initialError S.card < (J:ℚ)*largeRho S at budget
    linarith
  · obtain ⟨T,hT,hTJ,budget⟩ := large_sieve_budget (by omega : 1000000≤J) hS hB
    have loss := large_hit_total (J:=J) D hT hS hreg hb2
    have hcast : ((candidateSet D.ps J b).card:ℚ) ≤ ∑ p ∈ P, ((hitSet n p D.ps J b).card:ℚ) := by
      exact_mod_cast hc
    have combined := hcast.trans loss
    have herr := error_le_pow S.card
    by_cases h3 : 3∈S <;> simp only [h3,if_true,if_false] at combined budget <;> nlinarith

end A085265InclusionExclusion

namespace A085265Sieve

private theorem square_product_dvd (n : ℕ) (S : Finset ℕ)
    (h : ∀ p ∈ S, p.Prime ∧ p^2 ∣ n) : (∏ p ∈ S,p)^2 ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
    obtain ⟨pp,hd⟩ := h p (by simp)
    have hT : ∀ q ∈ T, q.Prime ∧ q^2 ∣ n := fun q hq => h q (by simp [hq])
    have hc : p.Coprime (∏ q ∈ T,q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply pp.coprime_iff_not_dvd.mpr
      exact fun hd => hp (((Nat.prime_dvd_prime_iff_eq pp (hT q hq).1).mp hd).symm ▸ hq)
    rw [Finset.prod_insert hp,mul_pow]
    exact ((hc.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd hd (ih hT)

theorem positive_square_general {n : ℕ} (hn : 0<n) (h₁ : n ≠ 1) (h₁₃ : n ≠ 13) :
    ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2) := by
  by_cases hsmall : n ≤ 365000
  · obtain ⟨k,hk,_,hlt,hs⟩ := squarefree_finite hn hsmall h₁ h₁₃
    exact ⟨k,hk,hlt,hs⟩
  let u := (n-1).sqrt
  let e : ℕ := if 4 ∣ n then 1 else 0
  let b : ℕ := if 4 ∣ n then 1 else 2
  let J := (u+e)/2
  let S := (Finset.range (n+1)).filter (fun p => 2<p ∧ p.Prime ∧ p^2∣n)
  have hu : 600 ≤ u := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hJ : 300 ≤ J := by dsimp only [J]; omega
  have hupper : (n-1).sqrt ≤ 2*J+1 := by change u ≤ 2*((u+e)/2)+1; omega
  have hb : b=1 ∨ b=2 := by unfold b; split <;> simp
  have hfit (x : ℕ) (hx : x<J) : (2*x+b)^2 < n := by
    have hku : 2*x+b ≤ u := by
      by_cases hc : 4∣n <;> simp only [J,b,e,hc,if_true,if_false] at hx ⊢ <;> omega
    have hs := Nat.le_sqrt'.mp hku
    omega
  have hS : ∀ p ∈ S, 2<p ∧ p.Prime := by
    intro p hp
    obtain ⟨_,hl,pp,_⟩ := Finset.mem_filter.mp hp
    exact ⟨hl,pp⟩
  have hreg (p : ℕ) (hl : 2<p) (pp : p.Prime) : p∈S ↔ p^2∣n := by
    constructor
    · exact fun hp => (Finset.mem_filter.mp hp).2.2.2
    · intro hp
      have hpn : p ∣ n := (show p ∣ p^2 by simp [pow_two]).trans hp
      have := Nat.le_of_dvd hn hpn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hl,pp,hp⟩
  have hd := square_product_dvd n S (fun p hp => ⟨(hS p hp).2,(Finset.mem_filter.mp hp).2.2.2⟩)
  have hB : (∏ p ∈ S,p) ≤ 2*J+2 := by
    have hsq := Nat.le_of_dvd hn hd
    have hn' : n ≤ (u+1)^2 := by
      have := Nat.lt_succ_sqrt' (n-1)
      change n-1 < (u+1)^2 at this
      omega
    have hbu : (∏ p ∈ S,p) ≤ u+1 := by
      by_contra! hh
      have hbig := Nat.pow_le_pow_left (show u+2 ≤ ∏ p ∈ S,p by omega) 2
      nlinarith
    change u ≤ 2*J+1 at hupper
    omega
  have hpar (x : ℕ) (hx : x<J) : ¬4∣n-(2*x+b)^2 := by
    intro hbad
    have hlt := hfit x hx
    by_cases hc : 4∣n
    · have hs := Nat.dvd_sub hc hbad
      rw [show n-(n-(2*x+b)^2)=(2*x+b)^2 by omega] at hs
      have hb' : b=1 := by simp [b,hc]
      rw [hb',show (2*x+1)^2=4*(x*(x+1))+1 by ring] at hs
      omega
    · have hb' : b=2 := by simp [b,hc]
      have hs : 4 ∣ (2*x+b)^2 := ⟨(x+1)^2,by rw [hb']; ring⟩
      exact hc (by simpa only [Nat.sub_add_cancel hlt.le] using dvd_add hbad hs)
  obtain ⟨x,hx,hs⟩ := A085265InclusionExclusion.large_or_moderate_rep S hJ hb hS hreg hB hfit hupper hpar
  exact ⟨2*x+b,by omega,hfit x hx,hs⟩

end A085265Sieve

namespace A085265Sieve

theorem exclude_one_thirteen {n k : ℕ} (hk : 0 < k) (hkn : k^2 < n)
    (hs : Squarefree (n-k^2)) : n ≠ 1 ∧ n ≠ 13 := by
  have hk₁ : 0 < k^2 := pow_pos hk 2
  refine ⟨by omega,?_⟩
  rintro rfl
  have hsmall : k < 4 := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  have table : ∀ j : Fin 4, 0 < j.val → ¬ Squarefree (13-j.val^2) := by decide +kernel
  exact table ⟨k,hsmall⟩ hk hs

end A085265Sieve

theorem OMA.solution : type_of% @OMA.S_oeis_a085265.main := by
  intro n hn
  constructor
  · rintro ⟨s,k,hs,hsf,hk,he⟩
    have hdiff : n-k^2 = s := by omega
    exact A085265Sieve.exclude_one_thirteen hk (by omega) (hdiff.symm ▸ hsf)
  · rintro ⟨h₁,h₁₃⟩
    obtain ⟨k,hk,hkn,hs⟩ := A085265Sieve.positive_square_general hn h₁ h₁₃
    exact ⟨n-k^2,k,by omega,hs,hk,by omega⟩

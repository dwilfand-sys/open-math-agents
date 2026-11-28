import OMAStatements.S_oeis_a085265
import Mathlib

/-!
A positive square plus a positive squarefree integer. Statement formalized by
@niclorusso. Proof prepared by Codex for @dwilfand-sys. The initial range uses
finite bit masks, the intermediate range uses certified interval estimates,
and the infinite tail follows from a prime-square sieve. See Jiménez Urroz,
Expositiones Mathematicae 40 (2022), 665–678, for the related result allowing
a zero square, and Dudek and Platt, LMS Journal of Computation and Mathematics
18 (2015), for prime squares outside the residue class 1 modulo 4.
-/

/-!
Finite and infinite ranges for OEIS A085265, formalized by @niclorusso.
Proof prepared by Codex for @dwilfand-sys. This fork check isolates the
finite certificate in the full proof. Credit: @dwilfand-sys
-/

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

namespace OMA.R_oeis_a085265_R2

def H1 : Prop := ∀ n : ℕ, 0 < n → n ≤ 365000 → n ≠ 1 → n ≠ 13 →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

def H2 : Prop := ∀ n : ℕ, 365000 < n →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085265.main := by
  intro small large n hn
  constructor
  · rintro ⟨s,k,hs,hsf,hk,he⟩
    have hdiff : n-k^2 = s := by omega
    exact A085265Sieve.exclude_one_thirteen hk (by omega) (hdiff.symm ▸ hsf)
  · rintro ⟨h₁,h₁₃⟩
    have hex : ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2) := by
      by_cases h : n ≤ 365000
      · exact small n hn h h₁ h₁₃
      · exact large n (by omega)
    obtain ⟨k,hk,hkn,hs⟩ := hex
    exact ⟨n-k^2,k,by omega,hs,hk,by omega⟩

end OMA.R_oeis_a085265_R2

/-! Split the remaining positive-square range at the start of the large sieve.
The root statement was formalized by @niclorusso. Credit: @dwilfand-sys. -/

namespace OMA.R_oeis_a085265_R2_H2_R1

def H1 : Prop := ∀ n : ℕ, 365000 < n → n ≤ 4000000000000 →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

def H2 : Prop := ∀ n : ℕ, 4000000000000 < n →
  ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2)

theorem main : H1 → H2 → OMA.R_oeis_a085265_R2.H2 := by
  intro middle large n hn
  by_cases h : n ≤ 4000000000000
  · exact middle n hn h
  · exact large n (by omega)

end OMA.R_oeis_a085265_R2_H2_R1

/-!
A finite numerical sieve budget and the covering argument for the intermediate
range of A085265. If every candidate root fails, counting excluded roots must
give an obstruction at least as large as the lower bound on candidates.
The numerical statement rules out that inequality without reference to n.
Credit: @dwilfand-sys. Root statement formalized by @niclorusso.
-/

open scoped BigOperators

namespace OMA.R_oeis_a085265_R2_H2_R1_H1_R1

def H1 : Prop := ∀ (J : ℕ) (S : Finset ℕ), 300 ≤ J → J ≤ 1000000 →
    (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
    ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) < (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

def H2 : Prop := ∀ n : ℕ, 365000 < n → n ≤ 4000000000000 →
    (∀ k : ℕ, 0 < k → k^2 < n → ¬ Squarefree (n-k^2)) →
    ∃ (J : ℕ) (S : Finset ℕ), 300 ≤ J ∧ J ≤ 1000000 ∧
      (∀ p ∈ S, 2 < p ∧ p.Prime) ∧ (∏ p ∈ S, p) ≤ 2*J+2 ∧
      (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ)) ≤ ((∑ p ∈ ((Finset.range (2*J+1+1)).filter (fun p => 2 < p ∧ Nat.Prime p)) \ S,
        (2*J/(p^2)+1) : ℕ) : ℚ) + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))

theorem main : H1 → H2 → OMA.R_oeis_a085265_R2_H2_R1.H1 := by
  intro budget cover n hlo hhi
  by_contra none
  have fail (k : ℕ) (hk : 0 < k) (hkn : k^2 < n) : ¬ Squarefree (n-k^2) :=
    fun hs => none ⟨k,hk,hkn,hs⟩
  obtain ⟨J,S,hJ,hJ',hS,hprod,hcount⟩ := cover n hlo hhi fail
  exact (not_lt_of_ge hcount) (budget J S hJ hJ' hS hprod)

end OMA.R_oeis_a085265_R2_H2_R1_H1_R1

namespace FiniteRange

/-!
Finite part of A085265, through 365000. The root statement was formalized by
@niclorusso. The mask and its proof come from the full proof prepared by Codex.
Credit: @dwilfand-sys
-/

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

theorem checked : OMA.R_oeis_a085265_R2.H1 := by
  intro n hn hN h1 h13
  obtain ⟨k,hk,_,hlt,hs⟩ := A085265Sieve.squarefree_finite hn hN h1 h13
  exact ⟨k,hk,hlt,hs⟩

end FiniteRange

namespace LargeRange

/-!
The large range in OEIS A085265. Credit: @dwilfand-sys (proof prepared by
Codex). Statement by @niclorusso. The direct sieve uses the elementary
primorial bound and inclusion–exclusion for the prime-square obstructions.
J. Jiménez Urroz proved the nonnegative-square result (DOI 10.1016/j.exmath.2021.12.002).
Dudek and Platt cover numbers outside 1 modulo 4 (DOI 10.1112/S1461157015000297).
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
  | h J ih =>
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

namespace A085265InclusionExclusion

open A085265Sieve

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

theorem large_rep {n J b : ℕ} (S : Finset ℕ) (hJ : 1000000 ≤ J)
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
  obtain ⟨T,hT,hTJ,budget⟩ := large_sieve_budget hJ hS hB
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

theorem positive_square_large {n : ℕ} (hlarge : 4000000000000 < n) :
    ∃ k : ℕ, 0 < k ∧ k^2 < n ∧ Squarefree (n-k^2) := by
  have hn : 0 < n := by omega
  let u := (n-1).sqrt
  let e : ℕ := if 4 ∣ n then 1 else 0
  let b : ℕ := if 4 ∣ n then 1 else 2
  let J := (u+e)/2
  let S := (Finset.range (n+1)).filter (fun p => 2<p ∧ p.Prime ∧ p^2∣n)
  have hu : 2000000 ≤ u := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hJ : 1000000 ≤ J := by dsimp only [J]; omega
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
  obtain ⟨x,hx,hs⟩ := A085265InclusionExclusion.large_rep S hJ hb hS hreg hB hfit hupper hpar
  exact ⟨2*x+b,by omega,hfit x hx,hs⟩

end A085265Sieve

theorem checked : OMA.R_oeis_a085265_R2_H2_R1.H2 := by
  intro n hn
  exact A085265Sieve.positive_square_large hn

end LargeRange

namespace MiddleObstruction

/-!
The middle range in OEIS A085265. Assuming that every positive root fails,
we bound the candidate count above by the sum of its prime-square exclusions.
Credit: @dwilfand-sys (proof prepared by Codex). Statement by @niclorusso.
-/

open scoped BigOperators

namespace A085265Sieve

def largePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => 2 < p ∧ Nat.Prime p)

def largeRho (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1-1/(p:ℚ))

end A085265Sieve

namespace A085265InclusionExclusion

open A085265Sieve

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

theorem prime_divisor_odd {S : Finset ℕ} (D : PrimeEnumeration S)
    (hS : ∀ p ∈ S, 2<p ∧ p.Prime) {d : ℕ} (hd : d ∣ D.ps.prod) : Odd d := by
  have ho := odd_product_list D.ps (fun p hp => by
    obtain ⟨h2,hpr⟩ := hS p ((D.mem p).mp hp)
    exact hpr.odd_of_ne_two (by omega))
  apply Nat.odd_iff.mpr
  by_contra he
  have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
  exact ho.not_two_dvd_nat (h2.trans hd)

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

open A085265Sieve A085265InclusionExclusion

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

theorem checked : OMA.R_oeis_a085265_R2_H2_R1_H1_R1.H2 := by
  classical
  intro n hlo hhi failure
  have hn : 0 < n := by omega
  let u := (n-1).sqrt
  let e : ℕ := if 4 ∣ n then 1 else 0
  let b : ℕ := if 4 ∣ n then 1 else 2
  let J := (u+e)/2
  let S := (Finset.range (n+1)).filter (fun p => 2<p ∧ p.Prime ∧ p^2∣n)
  have hu : 600 ≤ u := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hJ : 300 ≤ J := by dsimp only [J]; omega
  have hutop : u < 2000000 := by
    by_contra! h
    have hs : 4000000000000 ≤ n-1 := Nat.le_sqrt'.mp (show 2000000 ≤ (n-1).sqrt from h)
    omega
  have hJtop : J ≤ 1000000 := by
    have he : e ≤ 1 := by dsimp [e]; split <;> omega
    dsimp only [J]
    omega
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
  refine ⟨J, S, hJ, hJtop, hS, hB, ?_⟩
  have hnone : ¬ ∃ x<J, Squarefree (n-(2*x+b)^2) := by
    rintro ⟨x,hx,hs⟩
    exact failure (2*x+b) (by rcases hb with h | h <;> omega) (hfit x hx) hs
  obtain ⟨D⟩ := prime_enumeration S hS
  let P := (largePrimeSet (2*J+1)) \ S
  have cover := cover_candidates D hreg hb hfit hupper hpar hnone
  have hc : (candidateSet D.ps J b).card ≤ ∑ p ∈ P, (hitSet n p D.ps J b).card :=
    (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have hb2 : b ≤ 2 := by rcases hb with h | h <;> omega
  have hh : (candidateSet D.ps J b).card ≤ ∑ p ∈ P, (2*J/(p^2)+1) := by
    refine hc.trans ?_
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hh,hno⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨h2,hpr⟩ := (Finset.mem_filter.mp hh).2
    exact hit_card_raw D.ps hpr h2 (fun h => hno ((hreg p h2 hpr).mpr h)) hb2
  have hcast : ((candidateSet D.ps J b).card : ℚ) ≤
      ((∑ p ∈ P, (2*J/(p^2)+1) : ℕ) : ℚ) := by exact_mod_cast hh
  change (J:ℚ) * largeRho S ≤ ((∑ p ∈ P, (2*J/(p^2)+1) : ℕ) : ℚ) + initialError S.card
  exact sub_le_iff_le_add.mp ((initial_candidates D b J hS hb).trans hcast)

end MiddleObstruction

namespace MiddleBudget

namespace A085265.DyadicPrimeCount

open Finset

def oddPrimesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun p => 2 < p ∧ p.Prime)

def oddPrimeCount (x : ℕ) : ℕ := (oddPrimesUpTo x).card

private lemma mem_oddPrimesUpTo {p x : ℕ} :
    p ∈ oddPrimesUpTo x ↔ p ≤ x ∧ 2 < p ∧ p.Prime := by
  simp [oddPrimesUpTo, Nat.lt_succ_iff]

/-- The primes newly counted between m and x divide the single binomial (x choose m). -/
theorem interval (m x e : ℕ) (hmx : m ≤ x) (hxm : x ≤ 2 * m)
    (he : 0 < e) (hpow : 2^e ≤ m + 1) :
    oddPrimeCount x ≤ oddPrimeCount m + x / e := by
  let T := oddPrimesUpTo x \ oddPrimesUpTo m
  have sub : oddPrimesUpTo m ⊆ oddPrimesUpTo x := by
    intro p hp
    obtain ⟨hpm, ho, hpr⟩ := mem_oddPrimesUpTo.mp hp
    exact mem_oddPrimesUpTo.mpr ⟨hpm.trans hmx, ho, hpr⟩
  have props {p : ℕ} (hp : p ∈ T) : m < p ∧ p ≤ x ∧ p.Prime := by
    obtain ⟨hx, hm⟩ := mem_sdiff.mp hp
    obtain ⟨hpx, ho, hpr⟩ := mem_oddPrimesUpTo.mp hx
    have hmp : m < p := by
      by_contra! h
      exact hm (mem_oddPrimesUpTo.mpr ⟨h, ho, hpr⟩)
    exact ⟨hmp, hpx, hpr⟩
  have hprod : (∏ p ∈ T, p) ∣ x.choose m := by
    apply Finset.prod_primes_dvd
    · exact fun p hp => (props hp).2.2.prime
    · intro p hp
      obtain ⟨hmp, hpx, hpr⟩ := props hp
      exact hpr.dvd_choose hmp (by omega) hpx
  have bound : (2 : ℕ) ^ (e * T.card) ≤ 2 ^ x := calc
    2 ^ (e * T.card) = ∏ _p ∈ T, 2 ^ e := by rw [pow_mul, prod_const]
    _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' fun _p hp => hpow.trans (props hp).1
    _ ≤ x.choose m := Nat.le_of_dvd (Nat.choose_pos hmx) hprod
    _ ≤ 2 ^ x := Nat.choose_le_two_pow x m
  have hd : T.card ≤ x / e := by
    apply (Nat.le_div_iff_mul_le he).mpr
    simpa only [Nat.mul_comm] using (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound
  have hcard : T.card + oddPrimeCount m = oddPrimeCount x :=
    card_sdiff_add_card_eq_card sub
  omega

theorem double (m e : ℕ) (he : 0 < e) (hpow : 2 ^ e ≤ m + 1) :
    oddPrimeCount (2*m) ≤ oddPrimeCount m + 2*m/e :=
  interval m (2*m) e (by omega) le_rfl he hpow

end A085265.DyadicPrimeCount

namespace A085265.DyadicPrimeCount

open Finset

private def smallPrimeMark (v : ℕ) : ℕ := if 2 < v ∧ v.Prime then 1 else 0

private def smallPrimeSegment (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | h+1 => smallPrimeSegment a h + smallPrimeMark (a+1+h)

private theorem smallPrimeCount_sum (a : ℕ) :
    oddPrimeCount a = ∑ i ∈ range (a+1), smallPrimeMark i := by
  simpa only [oddPrimeCount, oddPrimesUpTo, smallPrimeMark, Nat.cast_id] using
    (Finset.sum_boole (R := ℕ) (fun p : ℕ => 2 < p ∧ p.Prime) (range (a+1))).symm

private theorem smallPrimeSegment_sum (a h : ℕ) :
    (∑ i ∈ range h, smallPrimeMark (a+1+i)) = smallPrimeSegment a h := by
  induction h with
  | zero => simp [smallPrimeSegment]
  | succ h ih => rw [Finset.sum_range_succ, ih, smallPrimeSegment]

private def candidateMark (n d : ℕ) : ℕ :=
  if n ≤ 2 ∨ (1 < d ∧ d < n ∧ n % d = 0) then 0 else 1

private theorem smallPrimeMark_le_candidateMark (n d : ℕ) :
    smallPrimeMark n ≤ candidateMark n d := by
  by_cases hn : 2 < n ∧ n.Prime
  · have hkeep : ¬(n ≤ 2 ∨ (1 < d ∧ d < n ∧ n % d = 0)) := by
      rcases hn with ⟨hn,hpr⟩
      rintro (h | ⟨hd,hs,hm⟩)
      · omega
      · rcases (Nat.dvd_prime hpr).mp (Nat.dvd_of_mod_eq_zero hm) with h | h <;> omega
    simp [smallPrimeMark, candidateMark, hn, hkeep]
  · simp [smallPrimeMark, hn]

private def candidateSegment (a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | h+1, q => candidateSegment a h (q/128) + candidateMark (a+1+h) (q%128)

private theorem smallPrimeSegment_le_candidates (a h q : ℕ) :
    smallPrimeSegment a h ≤ candidateSegment a h q := by
  induction h generalizing q with
  | zero => exact Nat.le_refl 0
  | succ h ih =>
    exact Nat.add_le_add (ih (q/128)) (smallPrimeMark_le_candidateMark (a+1+h) (q%128))

private theorem smallPrimeAdvanceUpper (a h c d q : ℕ)
    (ha : oddPrimeCount a ≤ c) (hd : candidateSegment a h q = d) :
    oddPrimeCount (a+h) ≤ c+d := by
  have split : oddPrimeCount (a+h) = oddPrimeCount a + smallPrimeSegment a h := by
    rw [smallPrimeCount_sum (a+h), smallPrimeCount_sum a,
      show a+h+1 = a+1+h by omega, Finset.sum_range_add, smallPrimeSegment_sum]
  rw [split]
  exact Nat.add_le_add ha ((smallPrimeSegment_le_candidates a h q).trans_eq hd)

private theorem smallCountTo0 : oddPrimeCount 0 ≤ 0 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem smallCountTo64 : oddPrimeCount 64 ≤ 17 :=
  smallPrimeAdvanceUpper 0 64 0 17 0x2000800206080020008182000800206080020a08182000800206082820008182000800206080020e08182000828206080020008182
    smallCountTo0 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo128 : oddPrimeCount 128 ≤ 30 :=
  smallPrimeAdvanceUpper 64 64 17 13 0xa08002060800200081820e0800206080020a081820008382060828200081820008002060800200081820008282060838216081820a08002
    smallCountTo64 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo192 : oddPrimeCount 192 ≤ 42 :=
  smallPrimeAdvanceUpper 128 64 30 12 0x6080020e08182000800206085820a081820008002060828200081820e0800206080021a081820008282060800200081820a085820608002
    smallCountTo128 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo256 : oddPrimeCount 256 ≤ 53 :=
  smallPrimeAdvanceUpper 192 64 42 11 0x8182000800206083820a08182160800206082820e081821a08002060800200081820008282060800200081820a0868206080021608182
    smallCountTo192 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo320 : oddPrimeCount 320 ≤ 65 :=
  smallPrimeAdvanceUpper 256 64 53 12 0x838206080020a08182000800206082820008182000800206083822208182000828206086820e081820a08002060800200081820008582
    smallCountTo256 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo384 : oddPrimeCount 384 ≤ 75 :=
  smallPrimeAdvanceUpper 320 64 65 10 0x6088820a081820e08002060828200081821608382060800200081820008282060800226081820a08002060838200081821a080020608002
    smallCountTo320 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo448 : oddPrimeCount 448 ≤ 85 :=
  smallPrimeAdvanceUpper 384 64 75 10 0xa081820008882060828200081820008682060858200081820e08282060800200081820a0838206080020008182260800206080020a08182
    smallCountTo384 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo512 : oddPrimeCount 512 ≤ 96 :=
  smallPrimeAdvanceUpper 448 64 85 11 0x858206082820008182000800206080020e08182160828206080021a081820a08002060800222081820e0800206080020a081820008382
    smallCountTo448 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo576 : oddPrimeCount 576 ≤ 104 :=
  smallPrimeAdvanceUpper 512 64 96 8 0x6082821608182000800206088822e081821a08282060838200081820a0800206089820e08182000868206080020a0818200080020608282
    smallCountTo512 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo605 : oddPrimeCount 605 ≤ 109 :=
  smallPrimeAdvanceUpper 576 29 104 5 0x40c107042c1030400113040c10004141030400100040c105
    smallCountTo576 (by decide +kernel)

theorem base_605 : oddPrimeCount 605 ≤ 109 := smallCountTo605

set_option maxRecDepth 10000 in
private theorem smallCountTo611 : oddPrimeCount 611 ≤ 110 :=
  smallPrimeAdvanceUpper 605 6 109 1 0x100040c10d
    smallCountTo605 (by decide +kernel)

theorem base_611 : oddPrimeCount 611 ≤ 110 := smallCountTo611

set_option maxRecDepth 10000 in
private theorem smallCountTo615 : oddPrimeCount 615 ≤ 111 :=
  smallPrimeAdvanceUpper 611 4 110 1 0x400103
    smallCountTo611 (by decide +kernel)

theorem base_615 : oddPrimeCount 615 ≤ 111 := smallCountTo615

set_option maxRecDepth 10000 in
private theorem smallCountTo617 : oddPrimeCount 617 ≤ 112 :=
  smallPrimeAdvanceUpper 615 2 111 1 0x100
    smallCountTo615 (by decide +kernel)

theorem base_617 : oddPrimeCount 617 ≤ 112 := smallCountTo617

set_option maxRecDepth 10000 in
private theorem smallCountTo629 : oddPrimeCount 629 ≤ 113 :=
  smallPrimeAdvanceUpper 617 12 112 1 0x400103041c105040c111
    smallCountTo617 (by decide +kernel)

theorem base_629 : oddPrimeCount 629 ≤ 113 := smallCountTo629

set_option maxRecDepth 10000 in
private theorem smallCountTo641 : oddPrimeCount 641 ≤ 115 :=
  smallPrimeAdvanceUpper 629 12 113 2 0x4001030414107040c100
    smallCountTo629 (by decide +kernel)

theorem base_641 : oddPrimeCount 641 ≤ 115 := smallCountTo641

set_option maxRecDepth 10000 in
private theorem smallCountTo651 : oddPrimeCount 651 ≤ 117 :=
  smallPrimeAdvanceUpper 641 10 115 2 0x100040c100042c103
    smallCountTo641 (by decide +kernel)

theorem base_651 : oddPrimeCount 651 ≤ 117 := smallCountTo651

set_option maxRecDepth 10000 in
private theorem smallCountTo659 : oddPrimeCount 659 ≤ 119 :=
  smallPrimeAdvanceUpper 651 8 117 2 0x400105040c100
    smallCountTo651 (by decide +kernel)

theorem base_659 : oddPrimeCount 659 ≤ 119 := smallCountTo659

set_option maxRecDepth 10000 in
private theorem smallCountTo671 : oddPrimeCount 671 ≤ 120 :=
  smallPrimeAdvanceUpper 659 12 119 1 0x4001030414117040c10b
    smallCountTo659 (by decide +kernel)

theorem base_671 : oddPrimeCount 671 ≤ 120 := smallCountTo671

set_option maxRecDepth 10000 in
private theorem smallCountTo681 : oddPrimeCount 681 ≤ 122 :=
  smallPrimeAdvanceUpper 671 10 120 2 0x100040c100041c103
    smallCountTo671 (by decide +kernel)

theorem base_681 : oddPrimeCount 681 ≤ 122 := smallCountTo681

set_option maxRecDepth 10000 in
private theorem smallCountTo699 : oddPrimeCount 699 ≤ 124 :=
  smallPrimeAdvanceUpper 681 18 122 2 0x10004141030434100040c1050444103
    smallCountTo681 (by decide +kernel)

theorem base_699 : oddPrimeCount 699 ≤ 124 := smallCountTo699

set_option maxRecDepth 10000 in
private theorem smallCountTo731 : oddPrimeCount 731 ≤ 128 :=
  smallPrimeAdvanceUpper 699 32 124 4 0x400113040c1070400103045c105040c100041c1030414100040c111
    smallCountTo699 (by decide +kernel)

theorem base_731 : oddPrimeCount 731 ≤ 128 := smallCountTo731

set_option maxRecDepth 10000 in
private theorem smallCountTo759 : oddPrimeCount 759 ≤ 133 :=
  smallPrimeAdvanceUpper 731 28 128 5 0x400103042c100040c1000414103041c100040c1050400103
    smallCountTo731 (by decide +kernel)

theorem base_759 : oddPrimeCount 759 ≤ 133 := smallCountTo759

set_option maxRecDepth 10000 in
private theorem smallCountTo809 : oddPrimeCount 809 ≤ 139 :=
  smallPrimeAdvanceUpper 759 50 133 6 0x100041c1030434100040c1000414103044c10b040c1050400103041c10d040c1000444103042c105040c100
    smallCountTo759 (by decide +kernel)

theorem base_809 : oddPrimeCount 809 ≤ 139 := smallCountTo809

set_option maxRecDepth 10000 in
private theorem smallCountTo841 : oddPrimeCount 841 ≤ 145 :=
  smallPrimeAdvanceUpper 809 32 139 6 0x4001030414113040c10004001030400100040c1070414103040011d
    smallCountTo809 (by decide +kernel)

theorem base_841 : oddPrimeCount 841 ≤ 145 := smallCountTo841

set_option maxRecDepth 10000 in
private theorem smallCountTo881 : oddPrimeCount 881 ≤ 151 :=
  smallPrimeAdvanceUpper 841 40 145 6 0x40c105041c103045c100040c10004001030400105040c10b04341030414100040c100
    smallCountTo841 (by decide +kernel)

theorem base_881 : oddPrimeCount 881 ≤ 151 := smallCountTo881

set_option maxRecDepth 10000 in
private theorem smallCountTo939 : oddPrimeCount 939 ≤ 158 :=
  smallPrimeAdvanceUpper 881 58 151 7 0x100040c100041c103044c105040c11d04441030414100040c100042c103041c100040c10d04141030400107040c1050400103
    smallCountTo881 (by decide +kernel)

theorem base_939 : oddPrimeCount 939 ≤ 158 := smallCountTo939

set_option maxRecDepth 10000 in
private theorem smallCountTo1003 : oddPrimeCount 1003 ≤ 167 :=
  smallPrimeAdvanceUpper 939 64 158 9 0x400117040c10004341030400105040c107047c1030414100040c100041c103040010b040c1000414103045c100040c1050400103041c111
    smallCountTo939 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1017 : oddPrimeCount 1017 ≤ 169 :=
  smallPrimeAdvanceUpper 1003 14 167 2 0x103044c100040c1000414103
    smallCountTo1003 (by decide +kernel)

theorem base_1017 : oddPrimeCount 1017 ≤ 169 := smallCountTo1017

set_option maxRecDepth 10000 in
private theorem smallCountTo1081 : oddPrimeCount 1081 ≤ 179 :=
  smallPrimeAdvanceUpper 1017 64 169 10 0x400100040c10504341030400100040c1110400103041c105040c10004001030414107040c1000400103042c100040c11d04141030434117
    smallCountTo1017 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1101 : oddPrimeCount 1101 ≤ 183 :=
  smallPrimeAdvanceUpper 1081 20 179 4 0x40c10504001030400100040c100041c103
    smallCountTo1081 (by decide +kernel)

theorem base_1101 : oddPrimeCount 1101 ≤ 183 := smallCountTo1101

set_option maxRecDepth 10000 in
private theorem smallCountTo1165 : oddPrimeCount 1165 ≤ 191 :=
  smallPrimeAdvanceUpper 1101 64 183 8 0x400105040c100042c1030414100040c1130400103041c100040c10b04141030444107040c105047c1030400100040c10d044c1030400105
    smallCountTo1101 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1199 : oddPrimeCount 1199 ≤ 195 :=
  smallPrimeAdvanceUpper 1165 34 191 4 0x103041c100040c105042c1030400107040c10004741030400105040c10b
    smallCountTo1165 (by decide +kernel)

theorem base_1199 : oddPrimeCount 1199 ≤ 195 := smallCountTo1199

set_option maxRecDepth 10000 in
private theorem smallCountTo1263 : oddPrimeCount 1263 ≤ 204 :=
  smallPrimeAdvanceUpper 1199 64 195 9 0x4001030414111040c10704001030400117040c10004141030400100040c1050400103044410b040c11d0400103041c105040c1000434103
    smallCountTo1199 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1327 : oddPrimeCount 1327 ≤ 216 :=
  smallPrimeAdvanceUpper 1263 64 204 12 0x414107040c11f044c1030400100040c10004141030400100040c10504001030400100040c100041c1030434105040c10004001030414100
    smallCountTo1263 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1359 : oddPrimeCount 1359 ≤ 216 :=
  smallPrimeAdvanceUpper 1327 32 216 0 0x40c10b047c103041c10d040c1110414103044c107040c105045c103
    smallCountTo1327 (by decide +kernel)

theorem base_1359 : oddPrimeCount 1359 ≤ 216 := smallCountTo1359

set_option maxRecDepth 10000 in
private theorem smallCountTo1423 : oddPrimeCount 1423 ≤ 223 :=
  smallPrimeAdvanceUpper 1359 64 216 7 0x40011d040c10004941030400105040c10704001030414113040c10d041c103042c100040c11704141030400111040c1050434103041c100
    smallCountTo1359 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1487 : oddPrimeCount 1487 ≤ 235 :=
  smallPrimeAdvanceUpper 1423 64 223 12 0x40c10004001030400105040c100042c1030414100040c1000400103047c100040c10704141030434100040c105041c1030400100040c100
    smallCountTo1423 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1551 : oddPrimeCount 1551 ≤ 243 :=
  smallPrimeAdvanceUpper 1487 64 235 8 0x4001030400105040c100044c103041410b040c10004441030494107040c1000414103042c100040c1050474103045c100040c1070400103
    smallCountTo1487 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1557 : oddPrimeCount 1557 ≤ 244 :=
  smallPrimeAdvanceUpper 1551 6 243 1 0x1000414103
    smallCountTo1551 (by decide +kernel)

theorem base_1557 : oddPrimeCount 1557 ≤ 244 := smallCountTo1557

set_option maxRecDepth 10000 in
private theorem smallCountTo1621 : oddPrimeCount 1621 ≤ 256 :=
  smallPrimeAdvanceUpper 1557 64 244 12 0x400107040c1050400103040010b040c11304001030400105040c10704941030414100040c100041c1030400100040c10004141030400100
    smallCountTo1557 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1685 : oddPrimeCount 1685 ≤ 262 :=
  smallPrimeAdvanceUpper 1621 64 256 6 0x40c1050400103041c117040c100042c103047c105040c11104341030414100040c10b04001030400100040c1070414103045c129040c105
    smallCountTo1621 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1749 : oddPrimeCount 1749 ≤ 271 :=
  smallPrimeAdvanceUpper 1685 64 262 9 0x41c103044c100040c10004001030434105040c10004741030414111040c1000400103042c107040c10004141030494100040c1050400103
    smallCountTo1685 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1813 : oddPrimeCount 1813 ≤ 279 :=
  smallPrimeAdvanceUpper 1749 64 271 8 0x444100040c107040010304a4105040c11d041c1030414100040c10d04001030400100040c10b0414103041c100040c10504341030400107
    smallCountTo1749 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1829 : oddPrimeCount 1829 ≤ 280 :=
  smallPrimeAdvanceUpper 1813 16 279 1 0x40c11704441030400105040c11f
    smallCountTo1813 (by decide +kernel)

theorem base_1829 : oddPrimeCount 1829 ≤ 280 := smallCountTo1829

set_option maxRecDepth 10000 in
private theorem smallCountTo1893 : oddPrimeCount 1893 ≤ 289 :=
  smallPrimeAdvanceUpper 1829 64 280 9 0x400103041410b040c107044c103040012b040c1110414103042c100040c10504001030400100040c1000400103041c105040c100047c103
    smallCountTo1829 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1957 : oddPrimeCount 1957 ≤ 296 :=
  smallPrimeAdvanceUpper 1893 64 289 7 0x414107040c100042c1030400117040c1000414103044c111040c10504a41030400100040c10d041c1030474105040c10004001030414113
    smallCountTo1893 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2021 : oddPrimeCount 2021 ≤ 305 :=
  smallPrimeAdvanceUpper 1957 64 296 9 0x40c1250434103041c10b040c10004141030400107040c1050400103042c100040c10004001030400105040c10704001030414100040c12b
    smallCountTo1957 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2047 : oddPrimeCount 2047 ≤ 308 :=
  smallPrimeAdvanceUpper 2021 26 305 3 0x107040c1000400103044c105040c10004341030414117
    smallCountTo2021 (by decide +kernel)

theorem base_2047 : oddPrimeCount 2047 ≤ 308 := smallCountTo2047

set_option maxRecDepth 10000 in
private theorem smallCountTo2111 : oddPrimeCount 2111 ≤ 317 :=
  smallPrimeAdvanceUpper 2047 64 308 9 0x40c1070400103042c11d040c10004141030400113040c105047c1030400100040c1000400103041c105040c100042c1030414107040c100
    smallCountTo2047 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2175 : oddPrimeCount 2175 ≤ 325 :=
  smallPrimeAdvanceUpper 2111 64 317 8 0x400103047410d040c10b04141030400100040c10504001030400100040c113041c1030400105040c1110400103041410b040c10d04a4103
    smallCountTo2111 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2239 : oddPrimeCount 2239 ≤ 332 :=
  smallPrimeAdvanceUpper 2175 64 325 7 0x41c100040c1250414103042c107040c1050434103047c100040c10004bc1030400105040c10704001030414111040c117041c1030400100
    smallCountTo2175 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2303 : oddPrimeCount 2303 ≤ 341 :=
  smallPrimeAdvanceUpper 2239 64 332 9 0x40c10004141030434100040c1050494103041c11f040c10004001030400105040c12b04001030414100040c11d0400103040010b040c107
    smallCountTo2239 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2367 : oddPrimeCount 2367 ≤ 349 :=
  smallPrimeAdvanceUpper 2303 64 341 8 0x4141030400100040c105041c103042c117040c10d04441030400105040c10004001030414100040c10004341030400107040c1110414103
    smallCountTo2303 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2421 : oddPrimeCount 2421 ≤ 358 :=
  smallPrimeAdvanceUpper 2367 54 349 9 0x11704001030414100040c1000400103041c100040c10004141030400107040c10504741030400113040c10004a4103
    smallCountTo2367 (by decide +kernel)

theorem base_2421 : oddPrimeCount 2421 ≤ 358 := smallCountTo2421

set_option maxRecDepth 10000 in
private theorem smallCountTo2485 : oddPrimeCount 2485 ≤ 366 :=
  smallPrimeAdvanceUpper 2421 64 358 8 0x400105040c107042c1030414100040c100041c103040011f040c10b04141030400117040c1050400103041c100040c10004941030434105
    smallCountTo2421 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2549 : oddPrimeCount 2549 ≤ 372 :=
  smallPrimeAdvanceUpper 2485 64 366 6 0x40c11304bc103041410b040c1290400103045c10d040c1070414103042c100040c105041c1030400111040c12b04001030400105040c100
    smallCountTo2485 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2613 : oddPrimeCount 2613 ≤ 378 :=
  smallPrimeAdvanceUpper 2549 64 372 6 0x4001030414100040c10d042c1030444107040c11f0414103040011d040c10504341030400100040c107045c103044c105040c100041c103
    smallCountTo2549 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2677 : oddPrimeCount 2677 ≤ 387 :=
  smallPrimeAdvanceUpper 2613 64 378 9 0x414100040c10004ac103049410b040c1000414103041c113040c1050400103042c107040c10004001030400105040c11104001030414100
    smallCountTo2613 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2741 : oddPrimeCount 2741 ≤ 399 :=
  smallPrimeAdvanceUpper 2677 64 387 12 0x40c10704001030400100040c10004141030400125040c10504001030400100040c10b0400103041c105040c10004001030414107040c100
    smallCountTo2677 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2805 : oddPrimeCount 2805 ≤ 408 :=
  smallPrimeAdvanceUpper 2741 64 399 9 0x43410304a4100040c1000414103047c10b040c1050400103044412f040c100041c103042c105040c10004001030414100040c1000400103
    smallCountTo2741 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2869 : oddPrimeCount 2869 ≤ 415 :=
  smallPrimeAdvanceUpper 2805 64 408 7 0x41c135040c11d04141030400107040c105042c103044c100040c10004441030400105040c10704001030414100040c100041c10304bc113
    smallCountTo2805 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2933 : oddPrimeCount 2933 ≤ 422 :=
  smallPrimeAdvanceUpper 2869 64 415 7 0x40c10d0414103040012b040c1050400103041c10b040c10004341030400105040c10004a41030414100040c1170494103040011d040c107
    smallCountTo2869 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2951 : oddPrimeCount 2951 ≤ 423 :=
  smallPrimeAdvanceUpper 2933 18 422 1 0x105040c10004441030414107040c10d
    smallCountTo2933 (by decide +kernel)

theorem base_2951 : oddPrimeCount 2951 ≤ 423 := smallCountTo2951

set_option maxRecDepth 10000 in
private theorem smallCountTo3015 : oddPrimeCount 3015 ≤ 431 :=
  smallPrimeAdvanceUpper 2951 64 423 8 0x400103040010b040c10004141030400100040c1050434103042c113040c11d041c10304a4105040c1000400103041411f040c100045c103
    smallCountTo2951 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3079 : oddPrimeCount 3079 ≤ 439 :=
  smallPrimeAdvanceUpper 3015 64 431 8 0x41c100040c10004141030434107040c10504001030400111040c10b040010304ac105040c10704001030414100040c125041c1030444100
    smallCountTo3015 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3143 : oddPrimeCount 3143 ≤ 445 :=
  smallPrimeAdvanceUpper 3079 64 439 6 0x40c1000414103040010b040c105044c103041c11d040c10d0400103042c105040c10004001030414135040c11f0434103040012b040c107
    smallCountTo3079 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3207 : oddPrimeCount 3207 ≤ 452 :=
  smallPrimeAdvanceUpper 3143 64 445 7 0x41410304bc117040c105041c1030474100040c1000400103044c105040c10b04001030414100040c100047c103045c107040c1000414103
    smallCountTo3143 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3271 : oddPrimeCount 3271 ≤ 461 :=
  smallPrimeAdvanceUpper 3207 64 452 9 0x40010d040c1050400103040010b040c107040010304d4105040c129041c1030414111040c10004001030400100040c10d0414103041c100
    smallCountTo3207 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3335 : oddPrimeCount 3335 ≤ 469 :=
  smallPrimeAdvanceUpper 3271 64 461 8 0x40c10504741030444107040c113042c1030494105040c10004001030414100040c1070400103047c100040c10004141030400100040c105
    smallCountTo3271 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3399 : oddPrimeCount 3399 ≤ 477 :=
  smallPrimeAdvanceUpper 3335 64 469 8 0x4bc1030434100040c1000444103041c105040c10004001030414107040c1000400103042c11f040c11104141030400100040c10504ac103
    smallCountTo3335 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3463 : oddPrimeCount 3463 ≤ 484 :=
  smallPrimeAdvanceUpper 3399 64 477 7 0x44c129040c100041c1030400105040c10d042c1030414117040c12f0400103041c113040c10b04141030400107040c10504001030400100
    smallCountTo3399 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3527 : oddPrimeCount 3527 ≤ 491 :=
  smallPrimeAdvanceUpper 3463 64 484 7 0x40c1000400103045c105040c10704ec103041410b040c100041c1030434100040c11f0414103042c100040c1050400103041c10d040c100
    smallCountTo3463 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3591 : oddPrimeCount 3591 ≤ 501 :=
  smallPrimeAdvanceUpper 3527 64 491 10 0x4001030400105040c10004001030414100040c135042c1030400100040c107041410304ac100040c105041c1030400100040c1110494103
    smallCountTo3527 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3655 : oddPrimeCount 3655 ≤ 509 :=
  smallPrimeAdvanceUpper 3591 64 501 8 0x400105040c13b04341030414100040c11704001030400107040c1000414103044c100040c1050400103042c100040c10704a41030434105
    smallCountTo3591 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3707 : oddPrimeCount 3707 ≤ 516 :=
  smallPrimeAdvanceUpper 3655 52 509 7 0x40c100041c1030414113040c1000400103040010d040c11d0414103041c100040c10504001030400107040c10b
    smallCountTo3655 (by decide +kernel)

theorem base_3707 : oddPrimeCount 3707 ≤ 516 := smallCountTo3707

set_option maxRecDepth 10000 in
private theorem smallCountTo3771 : oddPrimeCount 3771 ≤ 524 :=
  smallPrimeAdvanceUpper 3707 64 516 8 0x40010304bc105040c10004f41030414100040c10704001030494100040c1130414103045c10b040c10504341030400135040c1000400103
    smallCountTo3707 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3835 : oddPrimeCount 3835 ≤ 531 :=
  smallPrimeAdvanceUpper 3771 64 524 7 0x41c105040c100044c1030414107040c1110400103040011d040c10004141030434125040c105042c1030400100040c12b041c1030400105
    smallCountTo3771 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3899 : oddPrimeCount 3899 ≤ 538 :=
  smallPrimeAdvanceUpper 3835 64 531 7 0x40c10b045c1030414100040c1000400103041c111040c100041410304d4107040c1050400103040010b040c10d04001030444105040c107
    smallCountTo3835 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3963 : oddPrimeCount 3963 ≤ 547 :=
  smallPrimeAdvanceUpper 3899 64 538 9 0x4bc1030414100040c100041c1030400100040c10004141030400100040c105047c103041c100040c100042c10304ec105040c1250444103
    smallCountTo3899 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4027 : oddPrimeCount 4027 ≤ 556 :=
  smallPrimeAdvanceUpper 3963 64 547 9 0x414100040c10b047410304a4117040c1070414103040010d040c105041c1030400100040c100044c1030400105040c10004001030414100
    smallCountTo3963 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4091 : oddPrimeCount 4091 ≤ 562 :=
  smallPrimeAdvanceUpper 4027 64 556 6 0x40c11d0494103042c107040c10d04141030400100040c1050400103047c111040c10704341030400105040c100041c103041413d040c100
    smallCountTo4027 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4095 : oddPrimeCount 4095 ≤ 563 :=
  smallPrimeAdvanceUpper 4091 4 562 1 0x400103
    smallCountTo4091 (by decide +kernel)

theorem base_4095 : oddPrimeCount 4095 ≤ 563 := smallCountTo4095

set_option maxRecDepth 10000 in
private theorem smallCountTo4159 : oddPrimeCount 4159 ≤ 572 :=
  smallPrimeAdvanceUpper 4095 64 563 9 0x444100040c10b0414103041c100040c105045c1030434107040c10004001030400105040c10004a4103041410b040c10704001030400100
    smallCountTo4095 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4223 : oddPrimeCount 4223 ≤ 577 :=
  smallPrimeAdvanceUpper 4159 64 572 5 0x40c1170414103042c12b040c1050400103049412f040c13504ec103041c105040c10d04001030414107040c100042c1030400100040c129
    smallCountTo4159 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4287 : oddPrimeCount 4287 ≤ 587 :=
  smallPrimeAdvanceUpper 4223 64 577 10 0x4141030400100040c105044c1030400100040c11f041c1030400105040c10004001030414111040c1000400103041c10b040c1000414103
    smallCountTo4223 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4351 : oddPrimeCount 4351 ≤ 593 :=
  smallPrimeAdvanceUpper 4287 64 587 6 0x400107040c1050400103042c10d040c13b047c103044c105040c10704741030414100040c13d041c1030400100040c12b04141030400113
    smallCountTo4287 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4407 : oddPrimeCount 4407 ≤ 598 :=
  smallPrimeAdvanceUpper 4351 56 593 5 0x40c1050400103041c100040c10b04441030400105040c11d04341030414129040c100045c1030400135040c1070414103
    smallCountTo4351 (by decide +kernel)

theorem base_4407 : oddPrimeCount 4407 ≤ 598 := smallCountTo4407

set_option maxRecDepth 10000 in
private theorem smallCountTo4471 : oddPrimeCount 4471 ≤ 606 :=
  smallPrimeAdvanceUpper 4407 64 598 8 0x40010b040c105041c1030400100040c11304ac103042c105040c11704001030414100040c10004f41030400107040c100041410304a4111
    smallCountTo4407 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4535 : oddPrimeCount 4535 ≤ 614 :=
  smallPrimeAdvanceUpper 4471 64 606 8 0x40c105042c1030400100040c107050c1030400105040c10b041c1030414100040c10d04001030400100040c1000414103041c117040c105
    smallCountTo4471 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4599 : oddPrimeCount 4599 ≤ 621 :=
  smallPrimeAdvanceUpper 4535 64 614 7 0x434103044c107040c10004001030474105040c12f04001030414100040c1070444103045c113040c10004141030434100040c1050400103
    smallCountTo4535 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4663 : oddPrimeCount 4663 ≤ 630 :=
  smallPrimeAdvanceUpper 4599 64 621 9 0x4ac100040c111042c103041c105040c11f04001030414107040c10b04a41030400100040c10004141030400100040c105040010304ec100
    smallCountTo4599 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4727 : oddPrimeCount 4727 ≤ 636 :=
  smallPrimeAdvanceUpper 4663 64 630 6 0x40c10d041c1030400105040c100047c103041412b040c1000434103041c125040c10004141030444107040c10504d41030400100040c11d
    smallCountTo4663 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4791 : oddPrimeCount 4791 ≤ 643 :=
  smallPrimeAdvanceUpper 4727 64 636 7 0x4001030400105040c107042c103041412f040c100041c103050c100040c10b0414103044c10d040c1050444103041c100040c1000400103
    smallCountTo4727 (by decide +kernel)

theorem base_4791 : oddPrimeCount 4791 ≤ 643 := smallCountTo4791

set_option maxRecDepth 10000 in
private theorem smallCountTo4855 : oddPrimeCount 4855 ≤ 649 :=
  smallPrimeAdvanceUpper 4791 64 643 6 0x400105040c1000400103041410b040c1110400103040013d040c1070414103042c100040c105041c10304bc11d040c1250434103045c105
    smallCountTo4791 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4919 : oddPrimeCount 4919 ≤ 656 :=
  smallPrimeAdvanceUpper 4855 64 649 7 0x40c12b0400103041411f040c100042c1030400107040c11304141030400143040c10504ec1030434100040c10704001030444105040c100
    smallCountTo4855 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4983 : oddPrimeCount 4983 ≤ 665 :=
  smallPrimeAdvanceUpper 4919 64 656 9 0x41c103041410d040c1000400103040010b040c1000414103041c100040c1050400103042c107040c10004001030400105040c10d0444103
    smallCountTo4919 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5047 : oddPrimeCount 5047 ≤ 674 :=
  smallPrimeAdvanceUpper 4983 64 665 9 0x414100040c1070400103044c100040c10004141030400100040c10504741030400100040c10b04bc103041c105040c100051c1030414107
    smallCountTo4983 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5111 : oddPrimeCount 5111 ≤ 682 :=
  smallPrimeAdvanceUpper 5047 64 674 8 0x40c100047c1030434100040c13d0414103049410b040c1050400103040010d040c100041c103042c105040c10004001030414100040c113
    smallCountTo5047 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5175 : oddPrimeCount 5175 ≤ 688 :=
  smallPrimeAdvanceUpper 5111 64 682 6 0x400103041c100040c12f0414103045c107040c105042c10304d4125040c100044c1030400105040c10704341030414100040c100041c103
    smallCountTo5111 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5239 : oddPrimeCount 5239 ≤ 696 :=
  smallPrimeAdvanceUpper 5175 64 688 8 0x47c100040c1470414103040011d040c1050400103041c10b040c12904001030434105040c111045c1030414100040c1000400103040010d
    smallCountTo5175 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5279 : oddPrimeCount 5279 ≤ 699 :=
  smallPrimeAdvanceUpper 5239 40 696 3 0x40c1070414103047413b040c105041c1030400113040c117042c1030400105040c100
    smallCountTo5239 (by decide +kernel)

theorem base_5279 : oddPrimeCount 5279 ≤ 699 := smallCountTo5279

set_option maxRecDepth 10000 in
private theorem smallCountTo5343 : oddPrimeCount 5343 ≤ 705 :=
  smallPrimeAdvanceUpper 5279 64 699 6 0x4001030414111040c10b050c1030400107040c1000414103040012f040c10504341030444100040c10705241030400105040c113041c103
    smallCountTo5279 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5407 : oddPrimeCount 5407 ≤ 712 :=
  smallPrimeAdvanceUpper 5343 64 705 7 0x414100040c10004d4103042c117040c11f0414103041c129040c105044c1030400107040c10004441030400105040c100042c1030414100
    smallCountTo5343 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5471 : oddPrimeCount 5471 ≤ 721 :=
  smallPrimeAdvanceUpper 5407 64 712 9 0x40c10704001030400100040c10b041410304f4100040c10504001030400100040c10d0400103041c105040c13504ac1030414107040c100
    smallCountTo5407 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5535 : oddPrimeCount 5535 ≤ 731 :=
  smallPrimeAdvanceUpper 5471 64 721 10 0x4341030400100040c1000414103042c111040c105045c1030400100040c100041c1030494105040c10004001030414100040c100042c103
    smallCountTo5471 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5599 : oddPrimeCount 5599 ≤ 737 :=
  smallPrimeAdvanceUpper 5535 64 731 6 0x41c11d040c1170414103047c107040c1050400103050c100040c11304001030400105040c10704001030414125040c100041c103047410b
    smallCountTo5535 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5663 : oddPrimeCount 5663 ≤ 745 :=
  smallPrimeAdvanceUpper 5599 64 737 8 0x40c10d0414103051c11f040c10504a4103041c100040c111043410304ac105040c10004001030414100040c10004001030400100040c107
    smallCountTo5599 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5727 : oddPrimeCount 5727 ≤ 752 :=
  smallPrimeAdvanceUpper 5663 64 745 7 0x4141030400135040c105041c1030434100040c10b04001030400105040c1290400103041410d040c10004741030400107040c13b0414103
    smallCountTo5663 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5791 : oddPrimeCount 5791 ≤ 759 :=
  smallPrimeAdvanceUpper 5727 64 752 7 0x44410b040c10504001030400100040c1070400103042c105040c10d041c1030414149040c11d045c10304d4100040c1000414103041c100
    smallCountTo5727 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5855 : oddPrimeCount 5855 ≤ 768 :=
  smallPrimeAdvanceUpper 5791 64 759 9 0x40c105042c1030400107040c10004941030400105040c10b04001030414100040c107044c1030434100040c10004141030400100040c105
    smallCountTo5791 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5865 : oddPrimeCount 5865 ≤ 770 :=
  smallPrimeAdvanceUpper 5855 10 768 2 0x100040c100042c103
    smallCountTo5855 (by decide +kernel)

theorem base_5865 : oddPrimeCount 5865 ≤ 770 := smallCountTo5865

set_option maxRecDepth 10000 in
private theorem smallCountTo5929 : oddPrimeCount 5929 ≤ 778 :=
  smallPrimeAdvanceUpper 5865 64 770 8 0x400100040c10704141030400100040c105041c10304ac147040c10004441030400105040c113045c103041413d040c11f04001030400107
    smallCountTo5865 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5993 : oddPrimeCount 5993 ≤ 782 :=
  smallPrimeAdvanceUpper 5929 64 778 4 0x40c1110414103040010d040c105044c103042c100040c10704ec103050c105040c12f041c103041412b040c100047c1030400135040c10d
    smallCountTo5929 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6057 : oddPrimeCount 6057 ≤ 789 :=
  smallPrimeAdvanceUpper 5993 64 782 7 0x414103041c111040c10504001030400107040c10b0434103044c105040c10004941030414100040c10704001030400117040c1000414103
    smallCountTo5993 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6121 : oddPrimeCount 6121 ≤ 797 :=
  smallPrimeAdvanceUpper 6057 64 789 8 0x52410b040c10504001030434100040c13b0400103041c105040c10004001030414107040c1000444103047c129040c10004141030474100
    smallCountTo6057 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6185 : oddPrimeCount 6185 ≤ 803 :=
  smallPrimeAdvanceUpper 6121 64 797 6 0x40c105042c1030400100040c111041c1030400105040c10b0400103041412f040c13d0400103041c11f040c10004141030494107040c105
    smallCountTo6121 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6249 : oddPrimeCount 6249 ≤ 811 :=
  smallPrimeAdvanceUpper 6185 64 803 8 0x45c10304a410b040c10004001030400105040c10704001030414100040c100041c1030434100040c1170414103044414f040c1050400103
    smallCountTo6185 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6313 : oddPrimeCount 6313 ≤ 820 :=
  smallPrimeAdvanceUpper 6249 64 811 9 0x41c10d040c100042c1030400105040c10004001030414100040c10b04f41030400113040c10704141030400100040c105041c103040013b
    smallCountTo6249 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6377 : oddPrimeCount 6377 ≤ 830 :=
  smallPrimeAdvanceUpper 6313 64 820 10 0x40c100051c1030400105040c10004341030414100040c1110400103042c107040c10004141030400100040c1050400103045c100040c107
    smallCountTo6313 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6441 : oddPrimeCount 6441 ≤ 835 :=
  smallPrimeAdvanceUpper 6377 64 830 5 0x4001030434105040c100041c1030414100040c125044c10304ac10d040c10b0414103041c100040c105040010304ec107040c12904bc103
    smallCountTo6377 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6505 : oddPrimeCount 6505 ≤ 841 :=
  smallPrimeAdvanceUpper 6441 64 835 6 0x444105040c1000400103041410b040c107045c1030474100040c1000414103042c100040c1050434103040012b040c149050c103041c105
    smallCountTo6441 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6569 : oddPrimeCount 6569 ≤ 848 :=
  smallPrimeAdvanceUpper 6505 64 841 7 0x40c11704441030414107040c100042c10304f4100040c12f0414103043411f040c10504001030400100040c14f041c1030400105040c100
    smallCountTo6505 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6633 : oddPrimeCount 6633 ≤ 854 :=
  smallPrimeAdvanceUpper 6569 64 848 6 0x4001030414100040c1000474103041c10b040c11304141030400107040c1050400103042c111040c10d04001030494105040c107044c103
    smallCountTo6569 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6657 : oddPrimeCount 6657 ≤ 856 :=
  smallPrimeAdvanceUpper 6633 24 854 2 0x414100040c11d041c103044413d040c1000414103
    smallCountTo6633 (by decide +kernel)

theorem base_6657 : oddPrimeCount 6657 ≤ 856 := smallCountTo6657

set_option maxRecDepth 10000 in
private theorem smallCountTo6721 : oddPrimeCount 6721 ≤ 866 :=
  smallPrimeAdvanceUpper 6657 64 856 10 0x400100040c10504ec103041c100040c10b040010304a4105040c10004001030414125040c1000400103044c100040c1070414103040010b
    smallCountTo6657 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6785 : oddPrimeCount 6785 ≤ 872 :=
  smallPrimeAdvanceUpper 6721 64 866 6 0x40c105041c10304d4100040c100045c103042c105040c11104ac103041411d040c1000400103050c107040c10d04141030400100040c105
    smallCountTo6721 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6849 : oddPrimeCount 6849 ≤ 880 :=
  smallPrimeAdvanceUpper 6785 64 872 8 0x42c1030400100040c10704341030400105040c10b041c1030414111040c11304001030400100040c1000414103041c100040c10504a4103
    smallCountTo6785 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6913 : oddPrimeCount 6913 ≤ 888 :=
  smallPrimeAdvanceUpper 6849 64 880 8 0x434107040c100044c1030400105040c1000400103041410d040c1070400103051c153040c13d04141030400143040c1050400103040011f
    smallCountTo6849 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6977 : oddPrimeCount 6977 ≤ 896 :=
  smallPrimeAdvanceUpper 6913 64 888 8 0x40c100042c103041c105040c10d04741030414107040c10b04d41030400100040c11104141030400100040c10504001030400113040c100
    smallCountTo6913 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7041 : oddPrimeCount 7041 ≤ 904 :=
  smallPrimeAdvanceUpper 6977 64 896 8 0x41c1030400105040c11d04001030414100040c10004bc103041c12b040c10004141030400107040c1050400103053c10d040c11f0400103
    smallCountTo6977 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7105 : oddPrimeCount 7105 ≤ 909 :=
  smallPrimeAdvanceUpper 7041 64 904 5 0x400105040c107042c1030414100040c117041c1030494100040c10b04141030400149040c105044c103041c129040c12f047c1030400105
    smallCountTo7041 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7169 : oddPrimeCount 7169 ≤ 915 :=
  smallPrimeAdvanceUpper 7105 64 909 6 0x40c1000434103041410b040c10004441030400100040c1070414103042c125040c105041c1030400117040c11104001030434105040c143
    smallCountTo7105 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7233 : oddPrimeCount 7233 ≤ 923 :=
  smallPrimeAdvanceUpper 7169 64 915 8 0x51c1030414100040c12b042c1030400107040c1000414103045c113040c10504001030400100040c1070400103047c105040c100041c103
    smallCountTo7169 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7297 : oddPrimeCount 7297 ≤ 929 :=
  smallPrimeAdvanceUpper 7233 64 923 6 0x414100040c10d0400103040010b040c1000414103041c135040c1050434103042c107040c11304741030400105040c125045c1030414100
    smallCountTo7233 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7361 : oddPrimeCount 7361 ≤ 936 :=
  smallPrimeAdvanceUpper 7297 64 929 7 0x40c107050c1030400100040c14704141030434100040c10504441030400100040c10b04a4103041c105040c10004001030414107040c111
    smallCountTo7297 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7425 : oddPrimeCount 7425 ≤ 940 :=
  smallPrimeAdvanceUpper 7361 64 936 4 0x49410304d4100040c149041410304bc10b040c105054c103044c100040c10d041c103042c105040c11f04001030414100040c1290434103
    smallCountTo7361 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7489 : oddPrimeCount 7489 ≤ 948 :=
  smallPrimeAdvanceUpper 7425 64 940 8 0x41c111040c100041410304ac107040c105042c103040011d040c10004001030444105040c107047c1030414100040c100041c1030400100
    smallCountTo7425 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7553 : oddPrimeCount 7553 ≤ 957 :=
  smallPrimeAdvanceUpper 7489 64 948 9 0x40c13b0414103040010d040c1050400103041c10b040c10005241030400105040c10004441030414100040c100044c1030400100040c107
    smallCountTo7489 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7617 : oddPrimeCount 7617 ≤ 966 :=
  smallPrimeAdvanceUpper 7553 64 957 9 0x4141030400100040c105041c103050c100040c100042c1030400105040c10004001030414147040c10b04001030400107040c1170414103
    smallCountTo7553 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7679 : oddPrimeCount 7679 ≤ 972 :=
  smallPrimeAdvanceUpper 7617 62 966 6 0x1130400103041411d040c10d0444103041c100040c10004141030400107040c105043410304bc14f040c10b04001030400105040c107
    smallCountTo7617 (by decide +kernel)

theorem base_7679 : oddPrimeCount 7679 ≤ 972 := smallCountTo7679

set_option maxRecDepth 10000 in
private theorem smallCountTo7743 : oddPrimeCount 7743 ≤ 981 :=
  smallPrimeAdvanceUpper 7679 64 972 9 0x4001030414100040c100041c10304ac100040c1000414103043410b040c1050400103041c100040c10004ec103042c105040c1470400103
    smallCountTo7679 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7807 : oddPrimeCount 7807 ≤ 986 :=
  smallPrimeAdvanceUpper 7743 64 981 5 0x41413d040c11704001030400100040c10704141030444113040c105041c103047c12b040c10d04001030400105040c10b04741030414125
    smallCountTo7743 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7871 : oddPrimeCount 7871 ≤ 992 :=
  smallPrimeAdvanceUpper 7807 64 986 6 0x40c14904341030400107040c10004141030400129040c1050444103040010b040c10704bc1030400105040c11d041c1030414100040c111
    smallCountTo7807 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7935 : oddPrimeCount 7935 ≤ 1001 :=
  smallPrimeAdvanceUpper 7871 64 992 9 0x4001030400100040c1000414103041c10d040c10504d41030400107040c100042c10304a4105040c10005641030414100040c1070400103
    smallCountTo7871 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7999 : oddPrimeCount 7999 ≤ 1006 :=
  smallPrimeAdvanceUpper 7935 64 1001 5 0x400111040c10d04141030400100040c1050524103044c100040c11f0434103041c105040c14f045c1030414107040c13d0400103042c113
    smallCountTo7935 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8063 : oddPrimeCount 8063 ≤ 1012 :=
  smallPrimeAdvanceUpper 7999 64 1006 6 0x40c13504141030400100040c10504001030434147040c117041c1030474105040c100042c103041410d040c1530400103041c100040c10b
    smallCountTo7999 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8127 : oddPrimeCount 8127 ≤ 1021 :=
  smallPrimeAdvanceUpper 8063 64 1012 9 0x4141030400107040c10504a4103040013b040c10004001030400105040c1070400103041410b040c100041c1030400117040c1000414103
    smallCountTo8063 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8191 : oddPrimeCount 8191 ≤ 1027 :=
  smallPrimeAdvanceUpper 8127 64 1021 6 0x42c12f040c105053c103041c111040c1000474103047c105040c12904001030414100040c100042c1030434100040c1070414103044c100
    smallCountTo8127 (by decide +kernel)

theorem base_8191 : oddPrimeCount 8191 ≤ 1027 := smallCountTo8191

end A085265.DyadicPrimeCount

/- Uniform prime-count bands for the positive-square and squarefree sieve.
The first five bands use 35 small exact counts. The other eight use one
dyadic prime-count estimate and the previous band's density. -/

namespace A085267.SameJ

open Finset A085265.DyadicPrimeCount

def bands : List (ℕ × ℕ × ℚ × ℚ) := [
  (300,420,(183/500:ℚ),(96911/500000:ℚ)),
  (421,599,(9/25:ℚ),(49013/250000:ℚ)),
  (600,1023,(9/25:ℚ),(98959/500000:ℚ)),
  (1024,2047,(7/20:ℚ),(199283/1000000:ℚ)),
  (2048,4095,(73/250:ℚ),(200323/1000000:ℚ)),
  (4096,8191,(3127/10000:ℚ),(41/200:ℚ)),
  (8192,16383,(3103/10000:ℚ),(41/200:ℚ)),
  (16384,32767,(2981/10000:ℚ),(41/200:ℚ)),
  (32768,65535,(353/1250:ℚ),(41/200:ℚ)),
  (65536,131071,(2663/10000:ℚ),(41/200:ℚ)),
  (131072,262143,(627/2500:ℚ),(41/200:ℚ)),
  (262144,524287,(1183/5000:ℚ),(41/200:ℚ)),
  (524288,1000000,(559/2500:ℚ),(41/200:ℚ))]

private theorem count_mono {u v : ℕ} (h : u ≤ v) : oddPrimeCount u ≤ oddPrimeCount v := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hr, hprime⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hr).trans_le
    (Nat.succ_le_succ h)), hprime⟩

private theorem from_seed {J lo x cnt num den : ℕ} (hj : lo ≤ J) (hx : 2*J+1 ≤ x)
    (hcount : oddPrimeCount x ≤ cnt) (hgrid : cnt*den ≤ num*lo) (hd : 0 < den) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ ((num:ℚ)/den)*(J:ℚ) := by
  have h := (Nat.mul_le_mul_right den ((count_mono hx).trans hcount)).trans
    (hgrid.trans (Nat.mul_le_mul_left num hj))
  rw [div_mul_eq_mul_div, le_div_iff₀ (show (0:ℚ)<den by exact_mod_cast hd)]
  exact_mod_cast h

private theorem odd_half (J : ℕ) :
    oddPrimeCount (J+1) ≤ oddPrimeCount (2*(J/2)+1) := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hr,h2,hpr⟩ := Finset.mem_filter.mp hp
  have hle := Finset.mem_range.mp hr
  obtain ⟨k,hk⟩ := hpr.odd_of_ne_two (by omega)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),h2,hpr⟩

private theorem dyadic_step (J e : ℕ) (he : 0 < e) (hp : 2^e ≤ J+2) :
    oddPrimeCount (2*J+1) ≤ oddPrimeCount (2*(J/2)+1) + (2*J+1)/e := by
  have est := A085265.DyadicPrimeCount.interval (J+1) (2*J+1) e (by omega) (by omega) he hp
  exact est.trans (Nat.add_le_add_right (odd_half J) _)

private theorem band_300 (J : ℕ) (hlo : 300 ≤ J) (hhi : J ≤ 420) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (183/500:ℚ)*(J:ℚ) := by
  by_cases he_302 : J ≤ 302
  · exact from_seed (lo:=300) (x:=605) (cnt:=109) (num:=183) (den:=500) (by omega) (by omega) base_605 (by decide) (by decide)
  by_cases he_305 : J ≤ 305
  · exact from_seed (lo:=303) (x:=611) (cnt:=110) (num:=183) (den:=500) (by omega) (by omega) base_611 (by decide) (by decide)
  by_cases he_307 : J ≤ 307
  · exact from_seed (lo:=306) (x:=615) (cnt:=111) (num:=183) (den:=500) (by omega) (by omega) base_615 (by decide) (by decide)
  by_cases he_308 : J ≤ 308
  · exact from_seed (lo:=308) (x:=617) (cnt:=112) (num:=183) (den:=500) (by omega) (by omega) base_617 (by decide) (by decide)
  by_cases he_314 : J ≤ 314
  · exact from_seed (lo:=309) (x:=629) (cnt:=113) (num:=183) (den:=500) (by omega) (by omega) base_629 (by decide) (by decide)
  by_cases he_320 : J ≤ 320
  · exact from_seed (lo:=315) (x:=641) (cnt:=115) (num:=183) (den:=500) (by omega) (by omega) base_641 (by decide) (by decide)
  by_cases he_325 : J ≤ 325
  · exact from_seed (lo:=321) (x:=651) (cnt:=117) (num:=183) (den:=500) (by omega) (by omega) base_651 (by decide) (by decide)
  by_cases he_329 : J ≤ 329
  · exact from_seed (lo:=326) (x:=659) (cnt:=119) (num:=183) (den:=500) (by omega) (by omega) base_659 (by decide) (by decide)
  by_cases he_335 : J ≤ 335
  · exact from_seed (lo:=330) (x:=671) (cnt:=120) (num:=183) (den:=500) (by omega) (by omega) base_671 (by decide) (by decide)
  by_cases he_340 : J ≤ 340
  · exact from_seed (lo:=336) (x:=681) (cnt:=122) (num:=183) (den:=500) (by omega) (by omega) base_681 (by decide) (by decide)
  by_cases he_349 : J ≤ 349
  · exact from_seed (lo:=341) (x:=699) (cnt:=124) (num:=183) (den:=500) (by omega) (by omega) base_699 (by decide) (by decide)
  by_cases he_365 : J ≤ 365
  · exact from_seed (lo:=350) (x:=731) (cnt:=128) (num:=183) (den:=500) (by omega) (by omega) base_731 (by decide) (by decide)
  by_cases he_379 : J ≤ 379
  · exact from_seed (lo:=366) (x:=759) (cnt:=133) (num:=183) (den:=500) (by omega) (by omega) base_759 (by decide) (by decide)
  by_cases he_404 : J ≤ 404
  · exact from_seed (lo:=380) (x:=809) (cnt:=139) (num:=183) (den:=500) (by omega) (by omega) base_809 (by decide) (by decide)
  exact from_seed (lo:=405) (x:=841) (cnt:=145) (num:=183) (den:=500) (by omega) (by omega) base_841 (by decide) (by decide)

private theorem band_421 (J : ℕ) (hlo : 421 ≤ J) (hhi : J ≤ 599) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (9/25:ℚ)*(J:ℚ) := by
  by_cases he_440 : J ≤ 440
  · exact from_seed (lo:=421) (x:=881) (cnt:=151) (num:=9) (den:=25) (by omega) (by omega) base_881 (by decide) (by decide)
  by_cases he_469 : J ≤ 469
  · exact from_seed (lo:=441) (x:=939) (cnt:=158) (num:=9) (den:=25) (by omega) (by omega) base_939 (by decide) (by decide)
  by_cases he_508 : J ≤ 508
  · exact from_seed (lo:=470) (x:=1017) (cnt:=169) (num:=9) (den:=25) (by omega) (by omega) base_1017 (by decide) (by decide)
  by_cases he_550 : J ≤ 550
  · exact from_seed (lo:=509) (x:=1101) (cnt:=183) (num:=9) (den:=25) (by omega) (by omega) base_1101 (by decide) (by decide)
  exact from_seed (lo:=551) (x:=1199) (cnt:=195) (num:=9) (den:=25) (by omega) (by omega) base_1199 (by decide) (by decide)

private theorem band_600 (J : ℕ) (hlo : 600 ≤ J) (hhi : J ≤ 1023) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (9/25:ℚ)*(J:ℚ) := by
  by_cases he_679 : J ≤ 679
  · exact from_seed (lo:=600) (x:=1359) (cnt:=216) (num:=9) (den:=25) (by omega) (by omega) base_1359 (by decide) (by decide)
  by_cases he_778 : J ≤ 778
  · exact from_seed (lo:=680) (x:=1557) (cnt:=244) (num:=9) (den:=25) (by omega) (by omega) base_1557 (by decide) (by decide)
  by_cases he_914 : J ≤ 914
  · exact from_seed (lo:=779) (x:=1829) (cnt:=280) (num:=9) (den:=25) (by omega) (by omega) base_1829 (by decide) (by decide)
  exact from_seed (lo:=915) (x:=2047) (cnt:=308) (num:=9) (den:=25) (by omega) (by omega) base_2047 (by decide) (by decide)

private theorem band_1024 (J : ℕ) (hlo : 1024 ≤ J) (hhi : J ≤ 2047) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (7/20:ℚ)*(J:ℚ) := by
  by_cases he_1210 : J ≤ 1210
  · exact from_seed (lo:=1024) (x:=2421) (cnt:=358) (num:=7) (den:=20) (by omega) (by omega) base_2421 (by decide) (by decide)
  by_cases he_1475 : J ≤ 1475
  · exact from_seed (lo:=1211) (x:=2951) (cnt:=423) (num:=7) (den:=20) (by omega) (by omega) base_2951 (by decide) (by decide)
  by_cases he_1853 : J ≤ 1853
  · exact from_seed (lo:=1476) (x:=3707) (cnt:=516) (num:=7) (den:=20) (by omega) (by omega) base_3707 (by decide) (by decide)
  exact from_seed (lo:=1854) (x:=4095) (cnt:=563) (num:=7) (den:=20) (by omega) (by omega) base_4095 (by decide) (by decide)

private theorem band_2048 (J : ℕ) (hlo : 2048 ≤ J) (hhi : J ≤ 4095) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (73/250:ℚ)*(J:ℚ) := by
  by_cases he_2203 : J ≤ 2203
  · exact from_seed (lo:=2048) (x:=4407) (cnt:=598) (num:=73) (den:=250) (by omega) (by omega) base_4407 (by decide) (by decide)
  by_cases he_2395 : J ≤ 2395
  · exact from_seed (lo:=2204) (x:=4791) (cnt:=643) (num:=73) (den:=250) (by omega) (by omega) base_4791 (by decide) (by decide)
  by_cases he_2639 : J ≤ 2639
  · exact from_seed (lo:=2396) (x:=5279) (cnt:=699) (num:=73) (den:=250) (by omega) (by omega) base_5279 (by decide) (by decide)
  by_cases he_2932 : J ≤ 2932
  · exact from_seed (lo:=2640) (x:=5865) (cnt:=770) (num:=73) (den:=250) (by omega) (by omega) base_5865 (by decide) (by decide)
  by_cases he_3328 : J ≤ 3328
  · exact from_seed (lo:=2933) (x:=6657) (cnt:=856) (num:=73) (den:=250) (by omega) (by omega) base_6657 (by decide) (by decide)
  by_cases he_3839 : J ≤ 3839
  · exact from_seed (lo:=3329) (x:=7679) (cnt:=972) (num:=73) (den:=250) (by omega) (by omega) base_7679 (by decide) (by decide)
  exact from_seed (lo:=3840) (x:=8191) (cnt:=1027) (num:=73) (den:=250) (by omega) (by omega) base_8191 (by decide) (by decide)

private theorem band_4096 (J : ℕ) (hlo : 4096 ≤ J) (hhi : J ≤ 8191) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (3127/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 12 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/12 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_2048 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/12 : ℕ) : ℚ)*12 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 12
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (4096 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_8192 (J : ℕ) (hlo : 8192 ≤ J) (hhi : J ≤ 16383) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (3103/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 13 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/13 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_4096 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/13 : ℕ) : ℚ)*13 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 13
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (8192 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_16384 (J : ℕ) (hlo : 16384 ≤ J) (hhi : J ≤ 32767) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2981/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 14 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/14 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_8192 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/14 : ℕ) : ℚ)*14 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 14
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (16384 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_32768 (J : ℕ) (hlo : 32768 ≤ J) (hhi : J ≤ 65535) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (353/1250:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 15 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/15 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_16384 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/15 : ℕ) : ℚ)*15 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 15
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (32768 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_65536 (J : ℕ) (hlo : 65536 ≤ J) (hhi : J ≤ 131071) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (2663/10000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 16 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/16 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_32768 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/16 : ℕ) : ℚ)*16 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 16
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (65536 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_131072 (J : ℕ) (hlo : 131072 ≤ J) (hhi : J ≤ 262143) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (627/2500:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 17 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/17 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_65536 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/17 : ℕ) : ℚ)*17 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 17
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (131072 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_262144 (J : ℕ) (hlo : 262144 ≤ J) (hhi : J ≤ 524287) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (1183/5000:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 18 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/18 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_131072 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/18 : ℕ) : ℚ)*18 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 18
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (262144 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem band_524288 (J : ℕ) (hlo : 524288 ≤ J) (hhi : J ≤ 1000000) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ (559/2500:ℚ)*(J:ℚ) := by
  have step := dyadic_step J 19 (by decide) (by omega)
  have stepQ : (oddPrimeCount (2*J+1) : ℚ) ≤
      (oddPrimeCount (2*(J/2)+1) : ℚ) + (((2*J+1)/19 : ℕ) : ℚ) := by exact_mod_cast step
  have previous := band_262144 (J/2) (by omega) (by omega)
  have divQ : (((2*J+1)/19 : ℕ) : ℚ)*19 ≤ 2*(J:ℚ)+1 := by
    exact_mod_cast Nat.div_mul_le_self (2*J+1) 19
  have halfQ : 2*((J/2 : ℕ) : ℚ) ≤ J := by
    exact_mod_cast (show 2*(J/2) ≤ J by omega)
  have lowQ : (524288 : ℚ) ≤ J := by exact_mod_cast hlo
  linarith only [stepQ, previous, divQ, halfQ, lowQ]

private theorem all_bands : ∀ b ∈ bands, ∀ J : ℕ, b.1 ≤ J → J ≤ b.2.1 →
    (oddPrimeCount (2*J+1) : ℚ) ≤ b.2.2.1*(J:ℚ) := by
  unfold bands
  refine List.forall_mem_cons.mpr ⟨band_300, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_421, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_600, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_1024, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_2048, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_4096, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_8192, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_16384, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_32768, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_65536, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_131072, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_262144, ?_⟩
  refine List.forall_mem_cons.mpr ⟨band_524288, ?_⟩
  simp

theorem prime_count_le {lo hi J : ℕ} {alpha recip : ℚ}
    (hband : (lo,hi,alpha,recip) ∈ bands) (hlo : lo ≤ J) (hhi : J ≤ hi) :
    (oddPrimeCount (2*J+1) : ℚ) ≤ alpha*(J:ℚ) := all_bands _ hband J hlo hhi

theorem band_exists {J : ℕ} (hlo : 300 ≤ J) (hhi : J ≤ 1000000) :
    ∃ (lo hi : ℕ) (alpha recip : ℚ), (lo,hi,alpha,recip) ∈ bands ∧ lo ≤ J ∧ J ≤ hi := by
  by_cases until_420 : J ≤ 420
  · exact ⟨300,420,(183/500:ℚ),(96911/500000:ℚ),by unfold bands; exact (List.Mem.head _),by omega,by omega⟩
  by_cases until_599 : J ≤ 599
  · exact ⟨421,599,(9/25:ℚ),(49013/250000:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.head _)),by omega,by omega⟩
  by_cases until_1023 : J ≤ 1023
  · exact ⟨600,1023,(9/25:ℚ),(98959/500000:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),by omega,by omega⟩
  by_cases until_2047 : J ≤ 2047
  · exact ⟨1024,2047,(7/20:ℚ),(199283/1000000:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),by omega,by omega⟩
  by_cases until_4095 : J ≤ 4095
  · exact ⟨2048,4095,(73/250:ℚ),(200323/1000000:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),by omega,by omega⟩
  by_cases until_8191 : J ≤ 8191
  · exact ⟨4096,8191,(3127/10000:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))),by omega,by omega⟩
  by_cases until_16383 : J ≤ 16383
  · exact ⟨8192,16383,(3103/10000:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))),by omega,by omega⟩
  by_cases until_32767 : J ≤ 32767
  · exact ⟨16384,32767,(2981/10000:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))),by omega,by omega⟩
  by_cases until_65535 : J ≤ 65535
  · exact ⟨32768,65535,(353/1250:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))),by omega,by omega⟩
  by_cases until_131071 : J ≤ 131071
  · exact ⟨65536,131071,(2663/10000:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))),by omega,by omega⟩
  by_cases until_262143 : J ≤ 262143
  · exact ⟨131072,262143,(627/2500:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))),by omega,by omega⟩
  by_cases until_524287 : J ≤ 524287
  · exact ⟨262144,524287,(1183/5000:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))),by omega,by omega⟩
  exact ⟨524288,1000000,(559/2500:ℚ),(41/200:ℚ),by unfold bands; exact (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))),by omega,by omega⟩

end A085267.SameJ

/-! Same-parameter prime-square costs in the intermediate A085265 and A085267 sieve. -/

namespace A085265.SameJ

open Finset

def oddPrimes (x : ℕ) : Finset ℕ := (range (x+1)).filter (fun p => 2 < p ∧ p.Prime)
def active (J : ℕ) : Finset ℕ := (oddPrimes (2*J+1)).filter (fun p => p^2 ≤ 2*J)
def recip (A : Finset ℕ) : ℚ := ∑ p ∈ A, 1/(p:ℚ)^2

private lemma recip_mono {A B : Finset ℕ} (h : A ⊆ B) : recip A ≤ recip B :=
  sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

theorem mask_active {J : ℕ} {A : Finset ℕ} (hJ : 300 ≤ J)
    (hA : A ⊆ {3,5,7,11,13,17}) : A ⊆ active J := by
  intro p hp
  have tab : ∀ q ∈ ({3,5,7,11,13,17} : Finset ℕ), 2 < q ∧ q.Prime ∧ q ≤ 17 := by decide
  obtain ⟨h2,hprime,hle⟩ := tab p (hA hp)
  have sq := Nat.pow_le_pow_left hle 2
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), h2, hprime⟩, by omega⟩

theorem cost {J : ℕ} {S A : Finset ℕ} {α R : ℚ} (haS : A ⊆ S)
    (ha : A ⊆ active J) (hc : ((oddPrimes (2*J+1)).card : ℚ) ≤ α*(J:ℚ))
    (hr : recip (active J) ≤ R) :
    ((∑ p ∈ oddPrimes (2*J+1) \ S, (2*J/(p^2)+1) : ℕ) : ℚ) ≤
      (J:ℚ)*(α+2*(R-recip A))-(A.card:ℚ) := by
  let P := oddPrimes (2*J+1)
  let E := P \ S
  let B := E.filter (fun p => p^2 ≤ 2*J)
  have out {p : ℕ} (hp : p ∈ E) : p ∉ A :=
    fun h => (mem_sdiff.mp hp).2 (haS h)
  have disj : Disjoint E A := disjoint_left.mpr fun _ hp => out hp
  have bdisj : Disjoint B A := disjoint_left.mpr fun _ hp => out (mem_filter.mp hp).1
  have esub : E ∪ A ⊆ P := union_subset sdiff_subset (fun _ h => (mem_filter.mp (ha h)).1)
  have bsub : B ∪ A ⊆ active J := by
    apply union_subset _ ha
    intro p hp
    obtain ⟨he, hs⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_sdiff.mp he).1, hs⟩
  have rsum : recip B + recip A ≤ R := by
    calc
      _ = recip (B ∪ A) := (sum_union bdisj).symm
      _ ≤ _ := (recip_mono bsub).trans hr
  have csum : (E.card:ℚ) + (A.card:ℚ) ≤ α*(J:ℚ) := by
    have cn : E.card + A.card ≤ P.card := by
      rw [← card_union_of_disjoint disj]
      exact card_le_card esub
    exact (show (E.card:ℚ) + (A.card:ℚ) ≤ (P.card:ℚ) by exact_mod_cast cn).trans hc
  have remove : (∑ p ∈ B, 2*J/(p^2)) = ∑ p ∈ E, 2*J/(p^2) := by
    apply sum_subset (filter_subset _ _)
    intro p hp hn
    exact Nat.div_eq_of_lt (lt_of_not_ge (fun hs => hn (mem_filter.mpr ⟨hp,hs⟩)))
  have hf : ((∑ p ∈ E, 2*J/(p^2) : ℕ) : ℚ) ≤ 2*(J:ℚ)*(R-recip A) := by
    rw [← remove, Nat.cast_sum]
    calc
      _ ≤ ∑ p ∈ B, 2*(J:ℚ)*(1/(p:ℚ)^2) := by
        apply sum_le_sum
        intro p hp
        have hp0 : 0 < p := by
          have hodd := (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2.1
          omega
        rw [mul_one_div]
        apply (le_div_iff₀ (show 0 < (p:ℚ)^2 by positivity)).mpr
        exact_mod_cast Nat.div_mul_le_self (2*J) (p^2)
      _ = 2*(J:ℚ)*recip B := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [rsum]) (by positivity)
  change ((∑ p ∈ E, (2*J/(p^2)+1) : ℕ) : ℚ) ≤ _
  have card_weight : (∑ _p ∈ E, (1 : ℕ)) = E.card := by simp
  rw [sum_add_distrib, card_weight, Nat.cast_add]
  calc
    _ ≤ 2*(J:ℚ)*(R-recip A) + (α*(J:ℚ)-(A.card:ℚ)) :=
      add_le_add hf (le_sub_iff_add_le.mpr csum)
    _ = _ := by ring

private theorem active_recip_of_hi {J H T : ℕ} (hJ : J ≤ H) (hT : 2*H < (T+1)^2) :
    recip (active J) ≤ recip (oddPrimes T) := by
  apply recip_mono
  intro p hp
  obtain ⟨hmem,hs⟩ := mem_filter.mp hp
  have hle : p ≤ T := by
    by_contra! hh
    have bound := Nat.pow_le_pow_left (show T+1 ≤ p by omega) 2
    omega
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), (mem_filter.mp hmem).2⟩

theorem active_recip_420 {J : ℕ} (h : J ≤ 420) : recip (active J) ≤ 96911/500000 :=
  (active_recip_of_hi (T := 28) h (by decide)).trans (by decide +kernel)

theorem active_recip_599 {J : ℕ} (h : J ≤ 599) : recip (active J) ≤ 49013/250000 :=
  (active_recip_of_hi (T := 34) h (by decide)).trans (by decide +kernel)

theorem active_recip_1023 {J : ℕ} (h : J ≤ 1023) : recip (active J) ≤ 98959/500000 :=
  (active_recip_of_hi (T := 45) h (by decide)).trans (by decide +kernel)

theorem active_recip_2047 {J : ℕ} (h : J ≤ 2047) : recip (active J) ≤ 199283/1000000 :=
  (active_recip_of_hi (T := 63) h (by decide)).trans (by decide +kernel)

theorem active_recip_4095 {J : ℕ} (h : J ≤ 4095) : recip (active J) ≤ 200323/1000000 :=
  (active_recip_of_hi (T := 90) h (by decide)).trans (by decide +kernel)

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
    rw [← Finset.add_sum_erase P (fun q => 1/(q : ℚ)^2) hp]
    calc
      _ ≤ 1/(p : ℚ)^2 + 1/(2*(((p+1 : ℕ) : ℚ))) := add_le_add le_rfl htail
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using
        odd_reciprocal_step hT (hcut p hp)

/-- A finite subset of the odd primes past `T` has reciprocal-square sum at
most `1/(2T)`, by telescoping along successive odd integers. -/
theorem oddPrimeReciprocalTail {P : Finset ℕ} {T : ℕ} (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, 2 < p ∧ p.Prime) (hcut : ∀ p ∈ P, T < p) :
    (∑ p ∈ P, 1/(p : ℚ)^2) ≤ 1/(2*(T : ℚ)) :=
  odd_reciprocal_tail_aux P.card P rfl T hT hP hcut

theorem active_recip_global (J : ℕ) : recip (active J) ≤ 41/200 := by
  let Q := active J
  let low := Q.filter (fun p => p ≤ 128)
  let high := Q.filter (fun p => ¬p ≤ 128)
  have prop (p : ℕ) (hp : p ∈ Q) : 2 < p ∧ p.Prime :=
    (mem_filter.mp (mem_filter.mp hp).1).2
  have sub : low ⊆ oddPrimes 128 := by
    intro p hp
    obtain ⟨hq,hle⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), prop p hq⟩
  have tail : recip high ≤ 1/(2*(128:ℚ)) :=
    oddPrimeReciprocalTail (by decide) (fun p hp => prop p (mem_filter.mp hp).1)
      (fun _ hp => lt_of_not_ge (mem_filter.mp hp).2)
  have partition : recip low + recip high = recip Q :=
    sum_filter_add_sum_filter_not Q (fun p => p ≤ 128) (fun p => 1/(p:ℚ)^2)
  have finite : recip (oddPrimes 128) + 1/(2*(128:ℚ)) ≤ 41/200 := by decide +kernel
  exact partition ▸ (add_le_add (recip_mono sub) tail).trans finite

end A085265.SameJ

namespace A085267.SameJ

private theorem reciprocal_bands :
    ∀ b ∈ bands, ∀ J : ℕ, J ≤ b.2.1 →
      A085265.SameJ.recip (A085265.SameJ.active J) ≤ b.2.2.2 := by
  unfold bands
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_420 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_599 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_1023 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_2047 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun _ h => A085265.SameJ.active_recip_4095 h, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  refine List.forall_mem_cons.mpr ⟨fun J _ => A085265.SameJ.active_recip_global J, ?_⟩
  simp

theorem active_recip_le {lo hi J : ℕ} {α R : ℚ} (hb : (lo,hi,α,R) ∈ bands)
    (_hl : lo ≤ J) (hh : J ≤ hi) : A085265.SameJ.recip (A085265.SameJ.active J) ≤ R :=
  reciprocal_bands _ hb J hh

end A085267.SameJ

/- Fixed-J strict profile inequalities for the 13 bands. Each certificate checks
the first admissible J in its band and the nonnegative slope for all larger J. -/

namespace A085267.SameJ

open scoped BigOperators

private def profilePrimes : Finset ℕ := {3,5,7,11,13,17}

private def firstProfileJ (lo : ℕ) (A : Finset ℕ) (t : ℕ) : ℕ :=
  max lo (((∏ p ∈ A, p) * 19^t - 1) / 2)

private def profileError (k : ℕ) : ℚ := if k = 0 then 0 else (2:ℚ)^(k-1)

private def profileSlope (α R : ℚ) (A : Finset ℕ) (t : ℕ) : ℚ :=
  (∏ p ∈ A, (1-1/(p:ℚ))) * (18/19:ℚ)^t - (α + 2*(R-A085265.SameJ.recip A))

private def anchorProfile (row : ℕ × ℕ × ℚ × ℚ) : Prop :=
  ∀ A ∈ profilePrimes.powerset, ∀ t : Fin 5,
    firstProfileJ row.1 A t.val ≤ row.2.1 →
      0 ≤ profileSlope row.2.2.1 row.2.2.2 A t.val ∧
        1 + profileError (A.card+t.val) - (A.card:ℚ) <
          (firstProfileJ row.1 A t.val:ℚ) * profileSlope row.2.2.1 row.2.2.2 A t.val

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_300 :
    anchorProfile (300,420,(183/500:ℚ),(96911/500000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_421 :
    anchorProfile (421,599,(9/25:ℚ),(49013/250000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_600 :
    anchorProfile (600,1023,(9/25:ℚ),(98959/500000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_1024 :
    anchorProfile (1024,2047,(7/20:ℚ),(199283/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_2048 :
    anchorProfile (2048,4095,(73/250:ℚ),(200323/1000000:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_4096 :
    anchorProfile (4096,8191,(3127/10000:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_8192 :
    anchorProfile (8192,16383,(3103/10000:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_16384 :
    anchorProfile (16384,32767,(2981/10000:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_32768 :
    anchorProfile (32768,65535,(353/1250:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_65536 :
    anchorProfile (65536,131071,(2663/10000:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_131072 :
    anchorProfile (131072,262143,(627/2500:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_262144 :
    anchorProfile (262144,524287,(1183/5000:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem profileAnchor_524288 :
    anchorProfile (524288,1000000,(559/2500:ℚ),(41/200:ℚ)) := by
  unfold anchorProfile
  decide +kernel

private theorem allProfileAnchors : ∀ b ∈ bands, anchorProfile b := by
  unfold bands
  refine List.forall_mem_cons.mpr ⟨profileAnchor_300, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_421, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_600, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_1024, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_2048, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_4096, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_8192, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_16384, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_32768, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_65536, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_131072, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_262144, ?_⟩
  refine List.forall_mem_cons.mpr ⟨profileAnchor_524288, ?_⟩
  simp

theorem profile_all {lo hi J : ℕ} {α R : ℚ}
    (hband : (lo,hi,α,R) ∈ bands) (hlo : lo ≤ J) (hhi : J ≤ hi)
    (A : Finset ℕ) (hA : A ⊆ ({3,5,7,11,13,17} : Finset ℕ))
    (t : ℕ) (ht : t < 5) (hprod : (∏ p ∈ A, p) * 19^t ≤ 2*J+2) :
    (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) - (A.card:ℚ) +
      (1+(if A.card+t = 0 then 0 else (2:ℚ)^(A.card+t-1))) <
      (J:ℚ)*(∏ p ∈ A, (1-1/(p:ℚ)))*(18/19:ℚ)^t := by
  have hmin : firstProfileJ lo A t ≤ J := by
    unfold firstProfileJ
    exact max_le hlo (by omega)
  have hmem : A ∈ profilePrimes.powerset := Finset.mem_powerset.mpr hA
  obtain ⟨hslope, hanchor⟩ :=
    allProfileAnchors _ hband A hmem ⟨t,ht⟩ (hmin.trans hhi)
  change 0 ≤ profileSlope α R A t at hslope
  change 1 + profileError (A.card+t) - (A.card:ℚ) <
    (firstProfileJ lo A t:ℚ) * profileSlope α R A t at hanchor
  have hq : (firstProfileJ lo A t:ℚ) ≤ (J:ℚ) := by exact_mod_cast hmin
  have gap := hanchor.trans_le (mul_le_mul_of_nonneg_right hq hslope)
  change (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) - (A.card:ℚ) +
    (1+profileError (A.card+t)) < _
  calc
    _ = (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) +
        (1+profileError (A.card+t)-(A.card:ℚ)) := by ring
    _ < (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) +
        (J:ℚ)*profileSlope α R A t := by linarith only [gap]
    _ = _ := by unfold profileSlope; ring

end A085267.SameJ

open scoped BigOperators

namespace A085267.SameJ.Assembly

private def smallPrimes : Finset ℕ := {3, 5, 7, 11, 13, 17}

private def largeRho (A : Finset ℕ) : ℚ := ∏ p ∈ A, (1-1/(p:ℚ))

private def err (k : ℕ) : ℚ := if k = 0 then 0 else (2:ℚ)^(k-1)

private theorem rho_nonneg' {S : Finset ℕ} (h : ∀ p ∈ S, 2 < p) : 0 ≤ largeRho S := by
  apply Finset.prod_nonneg
  intro p hp
  have h₁ : (1:ℚ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := h p hp; omega)
  exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℚ) < p)).mpr h₁)

theorem combine {J : ℕ} {S : Finset ℕ} {α R : ℚ}
    (hlo : 300 ≤ J) (hhi : J ≤ 1000000) (hS : ∀ p ∈ S, 2 < p ∧ p.Prime)
    (hB : (∏ p ∈ S, p) ≤ 2*J+2)
    (hcount : ((A085265.SameJ.oddPrimes (2*J+1)).card : ℚ) ≤ α*(J:ℚ))
    (hrecip : A085265.SameJ.recip (A085265.SameJ.active J) ≤ R)
    (hprofile : ∀ A : Finset ℕ, A ⊆ smallPrimes → ∀ t : ℕ, t < 5 →
      (∏ p ∈ A, p) * 19^t ≤ 2*J+2 →
      (J:ℚ)*(α + 2*(R-A085265.SameJ.recip A)) - (A.card:ℚ) + (1+err (A.card+t)) <
        (J:ℚ)*largeRho A*(18/19:ℚ)^t) :
    ((∑ p ∈ A085265.SameJ.oddPrimes (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
      (1+err S.card) < (J:ℚ)*largeRho S := by
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
  have hright : (J:ℚ)*largeRho A*(18/19:ℚ)^T.card ≤ (J:ℚ)*largeRho S := calc
    _ = (J:ℚ)*(largeRho A*(18/19:ℚ)^T.card) := by ring
    _ ≤ (J:ℚ)*(largeRho A*largeRho T) := by gcongr
    _ = _ := by rw [hrho]
  have hsmall : A ⊆ smallPrimes := Finset.inter_subset_right
  have hactive : A ⊆ A085265.SameJ.active J := A085265.SameJ.mask_active hlo hsmall
  have lower := hprofile A hsmall T.card ht pA
  have upper := A085265.SameJ.cost haS hactive hcount hrecip
  rw [← card]
  exact ((add_le_add upper (le_refl (1+err (A.card+T.card)))).trans_lt lower).trans_le hright

end A085267.SameJ.Assembly

open scoped BigOperators

namespace A085267.SameJ.Assembly

theorem budget {J : ℕ} {S : Finset ℕ} (hlo : 300 ≤ J) (hhi : J ≤ 1000000)
    (hS : ∀ p ∈ S, 2 < p ∧ p.Prime) (hB : (∏ p ∈ S, p) ≤ 2*J+2) :
    ((∑ p ∈ A085265.SameJ.oddPrimes (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
      (1+(if S.card=0 then 0 else (2:ℚ)^(S.card-1))) <
        (J:ℚ)*(∏ p ∈ S, (1-1/(p:ℚ))) := by
  obtain ⟨lo, hi, α, R, hband, hlow, hhigh⟩ := A085267.SameJ.band_exists hlo hhi
  apply combine (α := α) (R := R) hlo hhi hS hB
  · exact A085267.SameJ.prime_count_le hband hlow hhigh
  · exact A085267.SameJ.active_recip_le hband hlow hhigh
  · intro A ha t ht hprod
    exact A085267.SameJ.profile_all hband hlow hhigh A ha t ht hprod

end A085267.SameJ.Assembly

theorem checked : OMA.R_oeis_a085265_R2_H2_R1_H1_R1.H1 := by
  intro J S hlo hhi hS hB
  have h := A085267.SameJ.Assembly.budget (J := J) (S := S) hlo hhi hS hB
  unfold A085265.SameJ.oddPrimes at h
  linarith only [h]

end MiddleBudget

theorem OMA.solution : type_of% @OMA.S_oeis_a085265.main :=
  OMA.R_oeis_a085265_R2.main FiniteRange.checked
    (OMA.R_oeis_a085265_R2_H2_R1.main
      (OMA.R_oeis_a085265_R2_H2_R1_H1_R1.main MiddleBudget.checked MiddleObstruction.checked)
      LargeRange.checked)

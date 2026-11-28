import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1
import Mathlib

/-!
Interval coverage and exact profile inequalities for the finite A085265 sieve.
Each interval supplies its strict comparison assuming its own upper bound.
Credit: @dwilfand-sys
-/

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

private theorem smallPrimeAdvance (a h c d : ℕ)
    (ha : oddPrimeCount a = c) (hd : smallPrimeSegment a h = d) :
    oddPrimeCount (a+h) = c+d := by
  have split : oddPrimeCount (a+h) = oddPrimeCount a + smallPrimeSegment a h := by
    rw [smallPrimeCount_sum (a+h), smallPrimeCount_sum a,
      show a+h+1 = a+1+h by omega, Finset.sum_range_add, smallPrimeSegment_sum]
  rw [split, ha, hd]

private theorem smallCountTo0 : oddPrimeCount 0 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo64 : oddPrimeCount 64 = 17 :=
  smallPrimeAdvance 0 64 0 17 smallCountTo0 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo128 : oddPrimeCount 128 = 30 :=
  smallPrimeAdvance 64 64 17 13 smallCountTo64 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo192 : oddPrimeCount 192 = 42 :=
  smallPrimeAdvance 128 64 30 12 smallCountTo128 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo256 : oddPrimeCount 256 = 53 :=
  smallPrimeAdvance 192 64 42 11 smallCountTo192 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo320 : oddPrimeCount 320 = 65 :=
  smallPrimeAdvance 256 64 53 12 smallCountTo256 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo384 : oddPrimeCount 384 = 75 :=
  smallPrimeAdvance 320 64 65 10 smallCountTo320 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo448 : oddPrimeCount 448 = 85 :=
  smallPrimeAdvance 384 64 75 10 smallCountTo384 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo512 : oddPrimeCount 512 = 96 :=
  smallPrimeAdvance 448 64 85 11 smallCountTo448 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo576 : oddPrimeCount 576 = 104 :=
  smallPrimeAdvance 512 64 96 8 smallCountTo512 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo615 : oddPrimeCount 615 = 111 :=
  smallPrimeAdvance 576 39 104 7 smallCountTo576 (by decide +kernel)

theorem base_615 : oddPrimeCount 615 ≤ 111 :=
  (smallCountTo615).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo629 : oddPrimeCount 629 = 113 :=
  smallPrimeAdvance 615 14 111 2 smallCountTo615 (by decide +kernel)

theorem base_629 : oddPrimeCount 629 ≤ 113 :=
  (smallCountTo629).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo647 : oddPrimeCount 647 = 117 :=
  smallPrimeAdvance 629 18 113 4 smallCountTo629 (by decide +kernel)

theorem base_647 : oddPrimeCount 647 ≤ 117 :=
  (smallCountTo647).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo665 : oddPrimeCount 665 = 120 :=
  smallPrimeAdvance 647 18 117 3 smallCountTo647 (by decide +kernel)

theorem base_665 : oddPrimeCount 665 ≤ 120 :=
  (smallCountTo665).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo683 : oddPrimeCount 683 = 123 :=
  smallPrimeAdvance 665 18 120 3 smallCountTo665 (by decide +kernel)

theorem base_683 : oddPrimeCount 683 ≤ 123 :=
  (smallCountTo683).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo711 : oddPrimeCount 711 = 126 :=
  smallPrimeAdvance 683 28 123 3 smallCountTo683 (by decide +kernel)

theorem base_711 : oddPrimeCount 711 ≤ 126 :=
  (smallCountTo711).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo737 : oddPrimeCount 737 = 129 :=
  smallPrimeAdvance 711 26 126 3 smallCountTo711 (by decide +kernel)

theorem base_737 : oddPrimeCount 737 ≤ 129 :=
  (smallCountTo737).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo771 : oddPrimeCount 771 = 135 :=
  smallPrimeAdvance 737 34 129 6 smallCountTo737 (by decide +kernel)

theorem base_771 : oddPrimeCount 771 ≤ 135 :=
  (smallCountTo771).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo819 : oddPrimeCount 819 = 140 :=
  smallPrimeAdvance 771 48 135 5 smallCountTo771 (by decide +kernel)

theorem base_819 : oddPrimeCount 819 ≤ 140 :=
  (smallCountTo819).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo861 : oddPrimeCount 861 = 148 :=
  smallPrimeAdvance 819 42 140 8 smallCountTo819 (by decide +kernel)

theorem base_861 : oddPrimeCount 861 ≤ 148 :=
  (smallCountTo861).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo909 : oddPrimeCount 909 = 154 :=
  smallPrimeAdvance 861 48 148 6 smallCountTo861 (by decide +kernel)

theorem base_909 : oddPrimeCount 909 ≤ 154 :=
  (smallCountTo909).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo969 : oddPrimeCount 969 = 162 :=
  smallPrimeAdvance 909 60 154 8 smallCountTo909 (by decide +kernel)

theorem base_969 : oddPrimeCount 969 ≤ 162 :=
  (smallCountTo969).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1033 : oddPrimeCount 1033 = 173 :=
  smallPrimeAdvance 969 64 162 11 smallCountTo969 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1035 : oddPrimeCount 1035 = 173 :=
  smallPrimeAdvance 1033 2 173 0 smallCountTo1033 (by decide +kernel)

theorem base_1035 : oddPrimeCount 1035 ≤ 173 :=
  (smallCountTo1035).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1099 : oddPrimeCount 1099 = 183 :=
  smallPrimeAdvance 1035 64 173 10 smallCountTo1035 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1101 : oddPrimeCount 1101 = 183 :=
  smallPrimeAdvance 1099 2 183 0 smallCountTo1099 (by decide +kernel)

theorem base_1101 : oddPrimeCount 1101 ≤ 183 :=
  (smallCountTo1101).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1165 : oddPrimeCount 1165 = 191 :=
  smallPrimeAdvance 1101 64 183 8 smallCountTo1101 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1185 : oddPrimeCount 1185 = 193 :=
  smallPrimeAdvance 1165 20 191 2 smallCountTo1165 (by decide +kernel)

theorem base_1185 : oddPrimeCount 1185 ≤ 193 :=
  (smallCountTo1185).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1249 : oddPrimeCount 1249 = 203 :=
  smallPrimeAdvance 1185 64 193 10 smallCountTo1185 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1287 : oddPrimeCount 1287 = 207 :=
  smallPrimeAdvance 1249 38 203 4 smallCountTo1249 (by decide +kernel)

theorem base_1287 : oddPrimeCount 1287 ≤ 207 :=
  (smallCountTo1287).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1351 : oddPrimeCount 1351 = 216 :=
  smallPrimeAdvance 1287 64 207 9 smallCountTo1287 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1415 : oddPrimeCount 1415 = 222 :=
  smallPrimeAdvance 1351 64 216 6 smallCountTo1351 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1421 : oddPrimeCount 1421 = 222 :=
  smallPrimeAdvance 1415 6 222 0 smallCountTo1415 (by decide +kernel)

theorem base_1421 : oddPrimeCount 1421 ≤ 222 :=
  (smallCountTo1421).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1485 : oddPrimeCount 1485 = 234 :=
  smallPrimeAdvance 1421 64 222 12 smallCountTo1421 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1549 : oddPrimeCount 1549 = 243 :=
  smallPrimeAdvance 1485 64 234 9 smallCountTo1485 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1565 : oddPrimeCount 1565 = 245 :=
  smallPrimeAdvance 1549 16 243 2 smallCountTo1549 (by decide +kernel)

theorem base_1565 : oddPrimeCount 1565 ≤ 245 :=
  (smallCountTo1565).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1629 : oddPrimeCount 1629 = 257 :=
  smallPrimeAdvance 1565 64 245 12 smallCountTo1565 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1693 : oddPrimeCount 1693 = 263 :=
  smallPrimeAdvance 1629 64 257 6 smallCountTo1629 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1731 : oddPrimeCount 1731 = 268 :=
  smallPrimeAdvance 1693 38 263 5 smallCountTo1693 (by decide +kernel)

theorem base_1731 : oddPrimeCount 1731 ≤ 268 :=
  (smallCountTo1731).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1795 : oddPrimeCount 1795 = 277 :=
  smallPrimeAdvance 1731 64 268 9 smallCountTo1731 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1859 : oddPrimeCount 1859 = 282 :=
  smallPrimeAdvance 1795 64 277 5 smallCountTo1795 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1923 : oddPrimeCount 1923 = 292 :=
  smallPrimeAdvance 1859 64 282 10 smallCountTo1859 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1929 : oddPrimeCount 1929 = 292 :=
  smallPrimeAdvance 1923 6 292 0 smallCountTo1923 (by decide +kernel)

theorem base_1929 : oddPrimeCount 1929 ≤ 292 :=
  (smallCountTo1929).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1993 : oddPrimeCount 1993 = 300 :=
  smallPrimeAdvance 1929 64 292 8 smallCountTo1929 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2057 : oddPrimeCount 2057 = 309 :=
  smallPrimeAdvance 1993 64 300 9 smallCountTo1993 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2121 : oddPrimeCount 2121 = 318 :=
  smallPrimeAdvance 2057 64 309 9 smallCountTo2057 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2165 : oddPrimeCount 2165 = 325 :=
  smallPrimeAdvance 2121 44 318 7 smallCountTo2121 (by decide +kernel)

theorem base_2165 : oddPrimeCount 2165 ≤ 325 :=
  (smallCountTo2165).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2229 : oddPrimeCount 2229 = 330 :=
  smallPrimeAdvance 2165 64 325 5 smallCountTo2165 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2293 : oddPrimeCount 2293 = 340 :=
  smallPrimeAdvance 2229 64 330 10 smallCountTo2229 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2357 : oddPrimeCount 2357 = 349 :=
  smallPrimeAdvance 2293 64 340 9 smallCountTo2293 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2421 : oddPrimeCount 2421 = 358 :=
  smallPrimeAdvance 2357 64 349 9 smallCountTo2357 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2457 : oddPrimeCount 2457 = 362 :=
  smallPrimeAdvance 2421 36 358 4 smallCountTo2421 (by decide +kernel)

theorem base_2457 : oddPrimeCount 2457 ≤ 362 :=
  (smallCountTo2457).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2521 : oddPrimeCount 2521 = 368 :=
  smallPrimeAdvance 2457 64 362 6 smallCountTo2457 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2585 : oddPrimeCount 2585 = 375 :=
  smallPrimeAdvance 2521 64 368 7 smallCountTo2521 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2649 : oddPrimeCount 2649 = 382 :=
  smallPrimeAdvance 2585 64 375 7 smallCountTo2585 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2713 : oddPrimeCount 2713 = 395 :=
  smallPrimeAdvance 2649 64 382 13 smallCountTo2649 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2777 : oddPrimeCount 2777 = 403 :=
  smallPrimeAdvance 2713 64 395 8 smallCountTo2713 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2801 : oddPrimeCount 2801 = 407 :=
  smallPrimeAdvance 2777 24 403 4 smallCountTo2777 (by decide +kernel)

theorem base_2801 : oddPrimeCount 2801 ≤ 407 :=
  (smallCountTo2801).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2865 : oddPrimeCount 2865 = 415 :=
  smallPrimeAdvance 2801 64 407 8 smallCountTo2801 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2929 : oddPrimeCount 2929 = 422 :=
  smallPrimeAdvance 2865 64 415 7 smallCountTo2865 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2993 : oddPrimeCount 2993 = 428 :=
  smallPrimeAdvance 2929 64 422 6 smallCountTo2929 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3057 : oddPrimeCount 3057 = 436 :=
  smallPrimeAdvance 2993 64 428 8 smallCountTo2993 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3121 : oddPrimeCount 3121 = 444 :=
  smallPrimeAdvance 3057 64 436 8 smallCountTo3057 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3185 : oddPrimeCount 3185 = 449 :=
  smallPrimeAdvance 3121 64 444 5 smallCountTo3121 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3249 : oddPrimeCount 3249 = 456 :=
  smallPrimeAdvance 3185 64 449 7 smallCountTo3185 (by decide +kernel)

theorem base_3249 : oddPrimeCount 3249 ≤ 456 :=
  (smallCountTo3249).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3313 : oddPrimeCount 3313 = 465 :=
  smallPrimeAdvance 3249 64 456 9 smallCountTo3249 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3377 : oddPrimeCount 3377 = 475 :=
  smallPrimeAdvance 3313 64 465 10 smallCountTo3313 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3441 : oddPrimeCount 3441 = 480 :=
  smallPrimeAdvance 3377 64 475 5 smallCountTo3377 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3505 : oddPrimeCount 3505 = 488 :=
  smallPrimeAdvance 3441 64 480 8 smallCountTo3441 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3569 : oddPrimeCount 3569 = 498 :=
  smallPrimeAdvance 3505 64 488 10 smallCountTo3505 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3633 : oddPrimeCount 3633 = 507 :=
  smallPrimeAdvance 3569 64 498 9 smallCountTo3569 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3697 : oddPrimeCount 3697 = 515 :=
  smallPrimeAdvance 3633 64 507 8 smallCountTo3633 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3761 : oddPrimeCount 3761 = 522 :=
  smallPrimeAdvance 3697 64 515 7 smallCountTo3697 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3771 : oddPrimeCount 3771 = 524 :=
  smallPrimeAdvance 3761 10 522 2 smallCountTo3761 (by decide +kernel)

theorem base_3771 : oddPrimeCount 3771 ≤ 524 :=
  (smallCountTo3771).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3835 : oddPrimeCount 3835 = 531 :=
  smallPrimeAdvance 3771 64 524 7 smallCountTo3771 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3899 : oddPrimeCount 3899 = 538 :=
  smallPrimeAdvance 3835 64 531 7 smallCountTo3835 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3963 : oddPrimeCount 3963 = 547 :=
  smallPrimeAdvance 3899 64 538 9 smallCountTo3899 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4027 : oddPrimeCount 4027 = 556 :=
  smallPrimeAdvance 3963 64 547 9 smallCountTo3963 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4091 : oddPrimeCount 4091 = 562 :=
  smallPrimeAdvance 4027 64 556 6 smallCountTo4027 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4155 : oddPrimeCount 4155 = 570 :=
  smallPrimeAdvance 4091 64 562 8 smallCountTo4091 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4219 : oddPrimeCount 4219 = 577 :=
  smallPrimeAdvance 4155 64 570 7 smallCountTo4155 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4283 : oddPrimeCount 4283 = 587 :=
  smallPrimeAdvance 4219 64 577 10 smallCountTo4219 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4347 : oddPrimeCount 4347 = 592 :=
  smallPrimeAdvance 4283 64 587 5 smallCountTo4283 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4411 : oddPrimeCount 4411 = 599 :=
  smallPrimeAdvance 4347 64 592 7 smallCountTo4347 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4427 : oddPrimeCount 4427 = 601 :=
  smallPrimeAdvance 4411 16 599 2 smallCountTo4411 (by decide +kernel)

theorem base_4427 : oddPrimeCount 4427 ≤ 601 :=
  (smallCountTo4427).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4491 : oddPrimeCount 4491 = 608 :=
  smallPrimeAdvance 4427 64 601 7 smallCountTo4427 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4555 : oddPrimeCount 4555 = 616 :=
  smallPrimeAdvance 4491 64 608 8 smallCountTo4491 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4619 : oddPrimeCount 4619 = 622 :=
  smallPrimeAdvance 4555 64 616 6 smallCountTo4555 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4683 : oddPrimeCount 4683 = 632 :=
  smallPrimeAdvance 4619 64 622 10 smallCountTo4619 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4747 : oddPrimeCount 4747 = 638 :=
  smallPrimeAdvance 4683 64 632 6 smallCountTo4683 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4811 : oddPrimeCount 4811 = 646 :=
  smallPrimeAdvance 4747 64 638 8 smallCountTo4747 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4875 : oddPrimeCount 4875 = 651 :=
  smallPrimeAdvance 4811 64 646 5 smallCountTo4811 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4939 : oddPrimeCount 4939 = 659 :=
  smallPrimeAdvance 4875 64 651 8 smallCountTo4875 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5003 : oddPrimeCount 5003 = 669 :=
  smallPrimeAdvance 4939 64 659 10 smallCountTo4939 (by decide +kernel)

theorem base_5003 : oddPrimeCount 5003 ≤ 669 :=
  (smallCountTo5003).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5022 : oddPrimeCount 5022 = 672 :=
  smallPrimeAdvance 5003 19 669 3 smallCountTo5003 (by decide +kernel)

theorem base_5022 : oddPrimeCount 5022 ≤ 672 :=
  (smallCountTo5022).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5086 : oddPrimeCount 5086 = 678 :=
  smallPrimeAdvance 5022 64 672 6 smallCountTo5022 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5096 : oddPrimeCount 5096 = 679 :=
  smallPrimeAdvance 5086 10 678 1 smallCountTo5086 (by decide +kernel)

theorem base_5096 : oddPrimeCount 5096 ≤ 679 :=
  (smallCountTo5096).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5122 : oddPrimeCount 5122 = 684 :=
  smallPrimeAdvance 5096 26 679 5 smallCountTo5096 (by decide +kernel)

theorem base_5122 : oddPrimeCount 5122 ≤ 684 :=
  (smallCountTo5122).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5174 : oddPrimeCount 5174 = 688 :=
  smallPrimeAdvance 5122 52 684 4 smallCountTo5122 (by decide +kernel)

theorem base_5174 : oddPrimeCount 5174 ≤ 688 :=
  (smallCountTo5174).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5177 : oddPrimeCount 5177 = 688 :=
  smallPrimeAdvance 5174 3 688 0 smallCountTo5174 (by decide +kernel)

theorem base_5177 : oddPrimeCount 5177 ≤ 688 :=
  (smallCountTo5177).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5218 : oddPrimeCount 5218 = 692 :=
  smallPrimeAdvance 5177 41 688 4 smallCountTo5177 (by decide +kernel)

theorem base_5218 : oddPrimeCount 5218 ≤ 692 :=
  (smallCountTo5218).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5256 : oddPrimeCount 5256 = 696 :=
  smallPrimeAdvance 5218 38 692 4 smallCountTo5218 (by decide +kernel)

theorem base_5256 : oddPrimeCount 5256 ≤ 696 :=
  (smallCountTo5256).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5318 : oddPrimeCount 5318 = 703 :=
  smallPrimeAdvance 5256 62 696 7 smallCountTo5256 (by decide +kernel)

theorem base_5318 : oddPrimeCount 5318 ≤ 703 :=
  (smallCountTo5318).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5366 : oddPrimeCount 5366 = 707 :=
  smallPrimeAdvance 5318 48 703 4 smallCountTo5318 (by decide +kernel)

theorem base_5366 : oddPrimeCount 5366 ≤ 707 :=
  (smallCountTo5366).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5385 : oddPrimeCount 5385 = 708 :=
  smallPrimeAdvance 5366 19 707 1 smallCountTo5366 (by decide +kernel)

theorem base_5385 : oddPrimeCount 5385 ≤ 708 :=
  (smallCountTo5385).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5449 : oddPrimeCount 5449 = 720 :=
  smallPrimeAdvance 5385 64 708 12 smallCountTo5385 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5459 : oddPrimeCount 5459 = 720 :=
  smallPrimeAdvance 5449 10 720 0 smallCountTo5449 (by decide +kernel)

theorem base_5459 : oddPrimeCount 5459 ≤ 720 :=
  (smallCountTo5459).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5474 : oddPrimeCount 5474 = 721 :=
  smallPrimeAdvance 5459 15 720 1 smallCountTo5459 (by decide +kernel)

theorem base_5474 : oddPrimeCount 5474 ≤ 721 :=
  (smallCountTo5474).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5502 : oddPrimeCount 5502 = 725 :=
  smallPrimeAdvance 5474 28 721 4 smallCountTo5474 (by decide +kernel)

theorem base_5502 : oddPrimeCount 5502 ≤ 725 :=
  (smallCountTo5502).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5504 : oddPrimeCount 5504 = 726 :=
  smallPrimeAdvance 5502 2 725 1 smallCountTo5502 (by decide +kernel)

theorem base_5504 : oddPrimeCount 5504 ≤ 726 :=
  (smallCountTo5504).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5541 : oddPrimeCount 5541 = 731 :=
  smallPrimeAdvance 5504 37 726 5 smallCountTo5504 (by decide +kernel)

theorem base_5541 : oddPrimeCount 5541 ≤ 731 :=
  (smallCountTo5541).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5561 : oddPrimeCount 5561 = 732 :=
  smallPrimeAdvance 5541 20 731 1 smallCountTo5541 (by decide +kernel)

theorem base_5561 : oddPrimeCount 5561 ≤ 732 :=
  (smallCountTo5561).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5605 : oddPrimeCount 5605 = 737 :=
  smallPrimeAdvance 5561 44 732 5 smallCountTo5561 (by decide +kernel)

theorem base_5605 : oddPrimeCount 5605 ≤ 737 :=
  (smallCountTo5605).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5617 : oddPrimeCount 5617 = 737 :=
  smallPrimeAdvance 5605 12 737 0 smallCountTo5605 (by decide +kernel)

theorem base_5617 : oddPrimeCount 5617 ≤ 737 :=
  (smallCountTo5617).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5621 : oddPrimeCount 5621 = 737 :=
  smallPrimeAdvance 5617 4 737 0 smallCountTo5617 (by decide +kernel)

theorem base_5621 : oddPrimeCount 5621 ≤ 737 :=
  (smallCountTo5621).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5659 : oddPrimeCount 5659 = 745 :=
  smallPrimeAdvance 5621 38 737 8 smallCountTo5621 (by decide +kernel)

theorem base_5659 : oddPrimeCount 5659 ≤ 745 :=
  (smallCountTo5659).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5723 : oddPrimeCount 5723 = 752 :=
  smallPrimeAdvance 5659 64 745 7 smallCountTo5659 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5743 : oddPrimeCount 5743 = 755 :=
  smallPrimeAdvance 5723 20 752 3 smallCountTo5723 (by decide +kernel)

theorem base_5743 : oddPrimeCount 5743 ≤ 755 :=
  (smallCountTo5743).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5754 : oddPrimeCount 5754 = 756 :=
  smallPrimeAdvance 5743 11 755 1 smallCountTo5743 (by decide +kernel)

theorem base_5754 : oddPrimeCount 5754 ≤ 756 :=
  (smallCountTo5754).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5765 : oddPrimeCount 5765 = 756 :=
  smallPrimeAdvance 5754 11 756 0 smallCountTo5754 (by decide +kernel)

theorem base_5765 : oddPrimeCount 5765 ≤ 756 :=
  (smallCountTo5765).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5771 : oddPrimeCount 5771 = 756 :=
  smallPrimeAdvance 5765 6 756 0 smallCountTo5765 (by decide +kernel)

theorem base_5771 : oddPrimeCount 5771 ≤ 756 :=
  (smallCountTo5771).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5835 : oddPrimeCount 5835 = 764 :=
  smallPrimeAdvance 5771 64 756 8 smallCountTo5771 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5899 : oddPrimeCount 5899 = 775 :=
  smallPrimeAdvance 5835 64 764 11 smallCountTo5835 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5907 : oddPrimeCount 5907 = 776 :=
  smallPrimeAdvance 5899 8 775 1 smallCountTo5899 (by decide +kernel)

theorem base_5907 : oddPrimeCount 5907 ≤ 776 :=
  (smallCountTo5907).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5940 : oddPrimeCount 5940 = 779 :=
  smallPrimeAdvance 5907 33 776 3 smallCountTo5907 (by decide +kernel)

theorem base_5940 : oddPrimeCount 5940 ≤ 779 :=
  (smallCountTo5940).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5951 : oddPrimeCount 5951 = 779 :=
  smallPrimeAdvance 5940 11 779 0 smallCountTo5940 (by decide +kernel)

theorem base_5951 : oddPrimeCount 5951 ≤ 779 :=
  (smallCountTo5951).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5980 : oddPrimeCount 5980 = 780 :=
  smallPrimeAdvance 5951 29 779 1 smallCountTo5951 (by decide +kernel)

theorem base_5980 : oddPrimeCount 5980 ≤ 780 :=
  (smallCountTo5980).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6026 : oddPrimeCount 6026 = 784 :=
  smallPrimeAdvance 5980 46 780 4 smallCountTo5980 (by decide +kernel)

theorem base_6026 : oddPrimeCount 6026 ≤ 784 :=
  (smallCountTo6026).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6059 : oddPrimeCount 6059 = 789 :=
  smallPrimeAdvance 6026 33 784 5 smallCountTo6026 (by decide +kernel)

theorem base_6059 : oddPrimeCount 6059 ≤ 789 :=
  (smallCountTo6059).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6123 : oddPrimeCount 6123 = 797 :=
  smallPrimeAdvance 6059 64 789 8 smallCountTo6059 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6147 : oddPrimeCount 6147 = 800 :=
  smallPrimeAdvance 6123 24 797 3 smallCountTo6123 (by decide +kernel)

theorem base_6147 : oddPrimeCount 6147 ≤ 800 :=
  (smallCountTo6147).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6150 : oddPrimeCount 6150 = 800 :=
  smallPrimeAdvance 6147 3 800 0 smallCountTo6147 (by decide +kernel)

theorem base_6150 : oddPrimeCount 6150 ≤ 800 :=
  (smallCountTo6150).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6208 : oddPrimeCount 6208 = 806 :=
  smallPrimeAdvance 6150 58 800 6 smallCountTo6150 (by decide +kernel)

theorem base_6208 : oddPrimeCount 6208 ≤ 806 :=
  (smallCountTo6208).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6259 : oddPrimeCount 6259 = 812 :=
  smallPrimeAdvance 6208 51 806 6 smallCountTo6208 (by decide +kernel)

theorem base_6259 : oddPrimeCount 6259 ≤ 812 :=
  (smallCountTo6259).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6271 : oddPrimeCount 6271 = 815 :=
  smallPrimeAdvance 6259 12 812 3 smallCountTo6259 (by decide +kernel)

theorem base_6271 : oddPrimeCount 6271 ≤ 815 :=
  (smallCountTo6271).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6315 : oddPrimeCount 6315 = 820 :=
  smallPrimeAdvance 6271 44 815 5 smallCountTo6271 (by decide +kernel)

theorem base_6315 : oddPrimeCount 6315 ≤ 820 :=
  (smallCountTo6315).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6322 : oddPrimeCount 6322 = 821 :=
  smallPrimeAdvance 6315 7 820 1 smallCountTo6315 (by decide +kernel)

theorem base_6322 : oddPrimeCount 6322 ≤ 821 :=
  (smallCountTo6322).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6351 : oddPrimeCount 6351 = 825 :=
  smallPrimeAdvance 6322 29 821 4 smallCountTo6322 (by decide +kernel)

theorem base_6351 : oddPrimeCount 6351 ≤ 825 :=
  (smallCountTo6351).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6359 : oddPrimeCount 6359 = 827 :=
  smallPrimeAdvance 6351 8 825 2 smallCountTo6351 (by decide +kernel)

theorem base_6359 : oddPrimeCount 6359 ≤ 827 :=
  (smallCountTo6359).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6398 : oddPrimeCount 6398 = 833 :=
  smallPrimeAdvance 6359 39 827 6 smallCountTo6359 (by decide +kernel)

theorem base_6398 : oddPrimeCount 6398 ≤ 833 :=
  (smallCountTo6398).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6413 : oddPrimeCount 6413 = 833 :=
  smallPrimeAdvance 6398 15 833 0 smallCountTo6398 (by decide +kernel)

theorem base_6413 : oddPrimeCount 6413 ≤ 833 :=
  (smallCountTo6413).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6444 : oddPrimeCount 6444 = 835 :=
  smallPrimeAdvance 6413 31 833 2 smallCountTo6413 (by decide +kernel)

theorem base_6444 : oddPrimeCount 6444 ≤ 835 :=
  (smallCountTo6444).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6508 : oddPrimeCount 6508 = 841 :=
  smallPrimeAdvance 6444 64 835 6 smallCountTo6444 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6527 : oddPrimeCount 6527 = 842 :=
  smallPrimeAdvance 6508 19 841 1 smallCountTo6508 (by decide +kernel)

theorem base_6527 : oddPrimeCount 6527 ≤ 842 :=
  (smallCountTo6527).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6584 : oddPrimeCount 6584 = 851 :=
  smallPrimeAdvance 6527 57 842 9 smallCountTo6527 (by decide +kernel)

theorem base_6584 : oddPrimeCount 6584 ≤ 851 :=
  (smallCountTo6584).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6634 : oddPrimeCount 6634 = 854 :=
  smallPrimeAdvance 6584 50 851 3 smallCountTo6584 (by decide +kernel)

theorem base_6634 : oddPrimeCount 6634 ≤ 854 :=
  (smallCountTo6634).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6661 : oddPrimeCount 6661 = 858 :=
  smallPrimeAdvance 6634 27 854 4 smallCountTo6634 (by decide +kernel)

theorem base_6661 : oddPrimeCount 6661 ≤ 858 :=
  (smallCountTo6661).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6694 : oddPrimeCount 6694 = 862 :=
  smallPrimeAdvance 6661 33 858 4 smallCountTo6661 (by decide +kernel)

theorem base_6694 : oddPrimeCount 6694 ≤ 862 :=
  (smallCountTo6694).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6695 : oddPrimeCount 6695 = 862 :=
  smallPrimeAdvance 6694 1 862 0 smallCountTo6694 (by decide +kernel)

theorem base_6695 : oddPrimeCount 6695 ≤ 862 :=
  (smallCountTo6695).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6759 : oddPrimeCount 6759 = 868 :=
  smallPrimeAdvance 6695 64 862 6 smallCountTo6695 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6797 : oddPrimeCount 6797 = 874 :=
  smallPrimeAdvance 6759 38 868 6 smallCountTo6759 (by decide +kernel)

theorem base_6797 : oddPrimeCount 6797 ≤ 874 :=
  (smallCountTo6797).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6827 : oddPrimeCount 6827 = 877 :=
  smallPrimeAdvance 6797 30 874 3 smallCountTo6797 (by decide +kernel)

theorem base_6827 : oddPrimeCount 6827 ≤ 877 :=
  (smallCountTo6827).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6872 : oddPrimeCount 6872 = 884 :=
  smallPrimeAdvance 6827 45 877 7 smallCountTo6827 (by decide +kernel)

theorem base_6872 : oddPrimeCount 6872 ≤ 884 :=
  (smallCountTo6872).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6924 : oddPrimeCount 6924 = 889 :=
  smallPrimeAdvance 6872 52 884 5 smallCountTo6872 (by decide +kernel)

theorem base_6924 : oddPrimeCount 6924 ≤ 889 :=
  (smallCountTo6924).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6929 : oddPrimeCount 6929 = 889 :=
  smallPrimeAdvance 6924 5 889 0 smallCountTo6924 (by decide +kernel)

theorem base_6929 : oddPrimeCount 6929 ≤ 889 :=
  (smallCountTo6929).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6937 : oddPrimeCount 6937 = 889 :=
  smallPrimeAdvance 6929 8 889 0 smallCountTo6929 (by decide +kernel)

theorem base_6937 : oddPrimeCount 6937 ≤ 889 :=
  (smallCountTo6937).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6955 : oddPrimeCount 6955 = 891 :=
  smallPrimeAdvance 6937 18 889 2 smallCountTo6937 (by decide +kernel)

theorem base_6955 : oddPrimeCount 6955 ≤ 891 :=
  (smallCountTo6955).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6962 : oddPrimeCount 6962 = 893 :=
  smallPrimeAdvance 6955 7 891 2 smallCountTo6955 (by decide +kernel)

theorem base_6962 : oddPrimeCount 6962 ≤ 893 :=
  (smallCountTo6962).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7026 : oddPrimeCount 7026 = 902 :=
  smallPrimeAdvance 6962 64 893 9 smallCountTo6962 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7047 : oddPrimeCount 7047 = 905 :=
  smallPrimeAdvance 7026 21 902 3 smallCountTo7026 (by decide +kernel)

theorem base_7047 : oddPrimeCount 7047 ≤ 905 :=
  (smallCountTo7047).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7079 : oddPrimeCount 7079 = 908 :=
  smallPrimeAdvance 7047 32 905 3 smallCountTo7047 (by decide +kernel)

theorem base_7079 : oddPrimeCount 7079 ≤ 908 :=
  (smallCountTo7079).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7143 : oddPrimeCount 7143 = 913 :=
  smallPrimeAdvance 7079 64 908 5 smallCountTo7079 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7207 : oddPrimeCount 7207 = 919 :=
  smallPrimeAdvance 7143 64 913 6 smallCountTo7143 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7225 : oddPrimeCount 7225 = 922 :=
  smallPrimeAdvance 7207 18 919 3 smallCountTo7207 (by decide +kernel)

theorem base_7225 : oddPrimeCount 7225 ≤ 922 :=
  (smallCountTo7225).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7227 : oddPrimeCount 7227 = 922 :=
  smallPrimeAdvance 7225 2 922 0 smallCountTo7225 (by decide +kernel)

theorem base_7227 : oddPrimeCount 7227 ≤ 922 :=
  (smallCountTo7227).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7228 : oddPrimeCount 7228 = 922 :=
  smallPrimeAdvance 7227 1 922 0 smallCountTo7227 (by decide +kernel)

theorem base_7228 : oddPrimeCount 7228 ≤ 922 :=
  (smallCountTo7228).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7292 : oddPrimeCount 7292 = 928 :=
  smallPrimeAdvance 7228 64 922 6 smallCountTo7228 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7294 : oddPrimeCount 7294 = 928 :=
  smallPrimeAdvance 7292 2 928 0 smallCountTo7292 (by decide +kernel)

theorem base_7294 : oddPrimeCount 7294 ≤ 928 :=
  (smallCountTo7294).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7306 : oddPrimeCount 7306 = 929 :=
  smallPrimeAdvance 7294 12 928 1 smallCountTo7294 (by decide +kernel)

theorem base_7306 : oddPrimeCount 7306 ≤ 929 :=
  (smallCountTo7306).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7370 : oddPrimeCount 7370 = 937 :=
  smallPrimeAdvance 7306 64 929 8 smallCountTo7306 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7374 : oddPrimeCount 7374 = 937 :=
  smallPrimeAdvance 7370 4 937 0 smallCountTo7370 (by decide +kernel)

theorem base_7374 : oddPrimeCount 7374 ≤ 937 :=
  (smallCountTo7374).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7419 : oddPrimeCount 7419 = 940 :=
  smallPrimeAdvance 7374 45 937 3 smallCountTo7374 (by decide +kernel)

theorem base_7419 : oddPrimeCount 7419 ≤ 940 :=
  (smallCountTo7419).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7448 : oddPrimeCount 7448 = 941 :=
  smallPrimeAdvance 7419 29 940 1 smallCountTo7419 (by decide +kernel)

theorem base_7448 : oddPrimeCount 7448 ≤ 941 :=
  (smallCountTo7448).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7477 : oddPrimeCount 7477 = 945 :=
  smallPrimeAdvance 7448 29 941 4 smallCountTo7448 (by decide +kernel)

theorem base_7477 : oddPrimeCount 7477 ≤ 945 :=
  (smallCountTo7477).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7523 : oddPrimeCount 7523 = 952 :=
  smallPrimeAdvance 7477 46 945 7 smallCountTo7477 (by decide +kernel)

theorem base_7523 : oddPrimeCount 7523 ≤ 952 :=
  (smallCountTo7523).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7527 : oddPrimeCount 7527 = 952 :=
  smallPrimeAdvance 7523 4 952 0 smallCountTo7523 (by decide +kernel)

theorem base_7527 : oddPrimeCount 7527 ≤ 952 :=
  (smallCountTo7527).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7578 : oddPrimeCount 7578 = 961 :=
  smallPrimeAdvance 7527 51 952 9 smallCountTo7527 (by decide +kernel)

theorem base_7578 : oddPrimeCount 7578 ≤ 961 :=
  (smallCountTo7578).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7642 : oddPrimeCount 7642 = 968 :=
  smallPrimeAdvance 7578 64 961 7 smallCountTo7578 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7667 : oddPrimeCount 7667 = 970 :=
  smallPrimeAdvance 7642 25 968 2 smallCountTo7642 (by decide +kernel)

theorem base_7667 : oddPrimeCount 7667 ≤ 970 :=
  (smallCountTo7667).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7680 : oddPrimeCount 7680 = 972 :=
  smallPrimeAdvance 7667 13 970 2 smallCountTo7667 (by decide +kernel)

theorem base_7680 : oddPrimeCount 7680 ≤ 972 :=
  (smallCountTo7680).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7683 : oddPrimeCount 7683 = 973 :=
  smallPrimeAdvance 7680 3 972 1 smallCountTo7680 (by decide +kernel)

theorem base_7683 : oddPrimeCount 7683 ≤ 973 :=
  (smallCountTo7683).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7747 : oddPrimeCount 7747 = 981 :=
  smallPrimeAdvance 7683 64 973 8 smallCountTo7683 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7811 : oddPrimeCount 7811 = 986 :=
  smallPrimeAdvance 7747 64 981 5 smallCountTo7747 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7813 : oddPrimeCount 7813 = 986 :=
  smallPrimeAdvance 7811 2 986 0 smallCountTo7811 (by decide +kernel)

theorem base_7813 : oddPrimeCount 7813 ≤ 986 :=
  (smallCountTo7813).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7829 : oddPrimeCount 7829 = 989 :=
  smallPrimeAdvance 7813 16 986 3 smallCountTo7813 (by decide +kernel)

theorem base_7829 : oddPrimeCount 7829 ≤ 989 :=
  (smallCountTo7829).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7843 : oddPrimeCount 7843 = 990 :=
  smallPrimeAdvance 7829 14 989 1 smallCountTo7829 (by decide +kernel)

theorem base_7843 : oddPrimeCount 7843 ≤ 990 :=
  (smallCountTo7843).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7875 : oddPrimeCount 7875 = 993 :=
  smallPrimeAdvance 7843 32 990 3 smallCountTo7843 (by decide +kernel)

theorem base_7875 : oddPrimeCount 7875 ≤ 993 :=
  (smallCountTo7875).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7939 : oddPrimeCount 7939 = 1002 :=
  smallPrimeAdvance 7875 64 993 9 smallCountTo7875 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8003 : oddPrimeCount 8003 = 1006 :=
  smallPrimeAdvance 7939 64 1002 4 smallCountTo7939 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8008 : oddPrimeCount 8008 = 1006 :=
  smallPrimeAdvance 8003 5 1006 0 smallCountTo8003 (by decide +kernel)

theorem base_8008 : oddPrimeCount 8008 ≤ 1006 :=
  (smallCountTo8008).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8047 : oddPrimeCount 8047 = 1010 :=
  smallPrimeAdvance 8008 39 1006 4 smallCountTo8008 (by decide +kernel)

theorem base_8047 : oddPrimeCount 8047 ≤ 1010 :=
  (smallCountTo8047).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8074 : oddPrimeCount 8074 = 1013 :=
  smallPrimeAdvance 8047 27 1010 3 smallCountTo8047 (by decide +kernel)

theorem base_8074 : oddPrimeCount 8074 ≤ 1013 :=
  (smallCountTo8074).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8088 : oddPrimeCount 8088 = 1015 :=
  smallPrimeAdvance 8074 14 1013 2 smallCountTo8074 (by decide +kernel)

theorem base_8088 : oddPrimeCount 8088 ≤ 1015 :=
  (smallCountTo8088).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8152 : oddPrimeCount 8152 = 1022 :=
  smallPrimeAdvance 8088 64 1015 7 smallCountTo8088 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8216 : oddPrimeCount 8216 = 1028 :=
  smallPrimeAdvance 8152 64 1022 6 smallCountTo8152 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8280 : oddPrimeCount 8280 = 1037 :=
  smallPrimeAdvance 8216 64 1028 9 smallCountTo8216 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8307 : oddPrimeCount 8307 = 1041 :=
  smallPrimeAdvance 8280 27 1037 4 smallCountTo8280 (by decide +kernel)

theorem base_8307 : oddPrimeCount 8307 ≤ 1041 :=
  (smallCountTo8307).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8371 : oddPrimeCount 8371 = 1047 :=
  smallPrimeAdvance 8307 64 1041 6 smallCountTo8307 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8420 : oddPrimeCount 8420 = 1051 :=
  smallPrimeAdvance 8371 49 1047 4 smallCountTo8371 (by decide +kernel)

theorem base_8420 : oddPrimeCount 8420 ≤ 1051 :=
  (smallCountTo8420).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8453 : oddPrimeCount 8453 = 1056 :=
  smallPrimeAdvance 8420 33 1051 5 smallCountTo8420 (by decide +kernel)

theorem base_8453 : oddPrimeCount 8453 ≤ 1056 :=
  (smallCountTo8453).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8517 : oddPrimeCount 8517 = 1060 :=
  smallPrimeAdvance 8453 64 1056 4 smallCountTo8453 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8547 : oddPrimeCount 8547 = 1065 :=
  smallPrimeAdvance 8517 30 1060 5 smallCountTo8517 (by decide +kernel)

theorem base_8547 : oddPrimeCount 8547 ≤ 1065 :=
  (smallCountTo8547).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8611 : oddPrimeCount 8611 = 1071 :=
  smallPrimeAdvance 8547 64 1065 6 smallCountTo8547 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8643 : oddPrimeCount 8643 = 1075 :=
  smallPrimeAdvance 8611 32 1071 4 smallCountTo8611 (by decide +kernel)

theorem base_8643 : oddPrimeCount 8643 ≤ 1075 :=
  (smallCountTo8643).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8707 : oddPrimeCount 8707 = 1084 :=
  smallPrimeAdvance 8643 64 1075 9 smallCountTo8643 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8716 : oddPrimeCount 8716 = 1085 :=
  smallPrimeAdvance 8707 9 1084 1 smallCountTo8707 (by decide +kernel)

theorem base_8716 : oddPrimeCount 8716 ≤ 1085 :=
  (smallCountTo8716).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8780 : oddPrimeCount 8780 = 1093 :=
  smallPrimeAdvance 8716 64 1085 8 smallCountTo8716 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8816 : oddPrimeCount 8816 = 1096 :=
  smallPrimeAdvance 8780 36 1093 3 smallCountTo8780 (by decide +kernel)

theorem base_8816 : oddPrimeCount 8816 ≤ 1096 :=
  (smallCountTo8816).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8880 : oddPrimeCount 8880 = 1105 :=
  smallPrimeAdvance 8816 64 1096 9 smallCountTo8816 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8925 : oddPrimeCount 8925 = 1108 :=
  smallPrimeAdvance 8880 45 1105 3 smallCountTo8880 (by decide +kernel)

theorem base_8925 : oddPrimeCount 8925 ≤ 1108 :=
  (smallCountTo8925).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8977 : oddPrimeCount 8977 = 1115 :=
  smallPrimeAdvance 8925 52 1108 7 smallCountTo8925 (by decide +kernel)

theorem base_8977 : oddPrimeCount 8977 ≤ 1115 :=
  (smallCountTo8977).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9041 : oddPrimeCount 9041 = 1122 :=
  smallPrimeAdvance 8977 64 1115 7 smallCountTo8977 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9061 : oddPrimeCount 9061 = 1125 :=
  smallPrimeAdvance 9041 20 1122 3 smallCountTo9041 (by decide +kernel)

theorem base_9061 : oddPrimeCount 9061 ≤ 1125 :=
  (smallCountTo9061).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9125 : oddPrimeCount 9125 = 1129 :=
  smallPrimeAdvance 9061 64 1125 4 smallCountTo9061 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9189 : oddPrimeCount 9189 = 1138 :=
  smallPrimeAdvance 9125 64 1129 9 smallCountTo9125 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9253 : oddPrimeCount 9253 = 1145 :=
  smallPrimeAdvance 9189 64 1138 7 smallCountTo9189 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9292 : oddPrimeCount 9292 = 1149 :=
  smallPrimeAdvance 9253 39 1145 4 smallCountTo9253 (by decide +kernel)

theorem base_9292 : oddPrimeCount 9292 ≤ 1149 :=
  (smallCountTo9292).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9356 : oddPrimeCount 9356 = 1157 :=
  smallPrimeAdvance 9292 64 1149 8 smallCountTo9292 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9420 : oddPrimeCount 9420 = 1164 :=
  smallPrimeAdvance 9356 64 1157 7 smallCountTo9356 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9422 : oddPrimeCount 9422 = 1165 :=
  smallPrimeAdvance 9420 2 1164 1 smallCountTo9420 (by decide +kernel)

theorem base_9422 : oddPrimeCount 9422 ≤ 1165 :=
  (smallCountTo9422).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9440 : oddPrimeCount 9440 = 1169 :=
  smallPrimeAdvance 9422 18 1165 4 smallCountTo9422 (by decide +kernel)

theorem base_9440 : oddPrimeCount 9440 ≤ 1169 :=
  (smallCountTo9440).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9504 : oddPrimeCount 9504 = 1176 :=
  smallPrimeAdvance 9440 64 1169 7 smallCountTo9440 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9568 : oddPrimeCount 9568 = 1182 :=
  smallPrimeAdvance 9504 64 1176 6 smallCountTo9504 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9611 : oddPrimeCount 9611 = 1184 :=
  smallPrimeAdvance 9568 43 1182 2 smallCountTo9568 (by decide +kernel)

theorem base_9611 : oddPrimeCount 9611 ≤ 1184 :=
  (smallCountTo9611).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9612 : oddPrimeCount 9612 = 1184 :=
  smallPrimeAdvance 9611 1 1184 0 smallCountTo9611 (by decide +kernel)

theorem base_9612 : oddPrimeCount 9612 ≤ 1184 :=
  (smallCountTo9612).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9676 : oddPrimeCount 9676 = 1192 :=
  smallPrimeAdvance 9612 64 1184 8 smallCountTo9612 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9740 : oddPrimeCount 9740 = 1200 :=
  smallPrimeAdvance 9676 64 1192 8 smallCountTo9676 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9754 : oddPrimeCount 9754 = 1202 :=
  smallPrimeAdvance 9740 14 1200 2 smallCountTo9740 (by decide +kernel)

theorem base_9754 : oddPrimeCount 9754 ≤ 1202 :=
  (smallCountTo9754).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9818 : oddPrimeCount 9818 = 1210 :=
  smallPrimeAdvance 9754 64 1202 8 smallCountTo9754 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9858 : oddPrimeCount 9858 = 1215 :=
  smallPrimeAdvance 9818 40 1210 5 smallCountTo9818 (by decide +kernel)

theorem base_9858 : oddPrimeCount 9858 ≤ 1215 :=
  (smallCountTo9858).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9922 : oddPrimeCount 9922 = 1221 :=
  smallPrimeAdvance 9858 64 1215 6 smallCountTo9858 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9948 : oddPrimeCount 9948 = 1225 :=
  smallPrimeAdvance 9922 26 1221 4 smallCountTo9922 (by decide +kernel)

theorem base_9948 : oddPrimeCount 9948 ≤ 1225 :=
  (smallCountTo9948).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9982 : oddPrimeCount 9982 = 1228 :=
  smallPrimeAdvance 9948 34 1225 3 smallCountTo9948 (by decide +kernel)

theorem base_9982 : oddPrimeCount 9982 ≤ 1228 :=
  (smallCountTo9982).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo10000 : oddPrimeCount 10000 = 1228 :=
  smallPrimeAdvance 9982 18 1228 0 smallCountTo9982 (by decide +kernel)

theorem base_10000 : oddPrimeCount 10000 ≤ 1228 :=
  (smallCountTo10000).le

end A085265.DyadicPrimeCount

open scoped BigOperators

namespace A085265Sieve

def largePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => 2 < p ∧ Nat.Prime p)

def largeRho (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1-1/(p:ℚ))

end A085265Sieve
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
  (4806, 5021, 3506),
  (5022, 5255, 3667),
  (5256, 5503, 3839),
  (5504, 5770, 4022),
  (5771, 6058, 4218),
  (6059, 6358, 4428),
  (6359, 6694, 4652),
  (6695, 7046, 4897),
  (7047, 7447, 5160),
  (7448, 7874, 5454),
  (7875, 8546, 5800),
  (8547, 9291, 6298),
  (9292, 9999, 6771),
  (10000, 10353, 7292),
  (10354, 10730, 7551),
  (10731, 11120, 7826),
  (11121, 11529, 8112),
  (11530, 11959, 8412),
  (11960, 12415, 8728),
  (12416, 12887, 9061),
  (12888, 13387, 9407),
  (13388, 13909, 9771),
  (13910, 14455, 10155),
  (14456, 15045, 10557),
  (15046, 15657, 10986),
  (15658, 16838, 11516),
  (16839, 18121, 12386),
  (18122, 19507, 13329),
  (19508, 20487, 14275),
  (20488, 21536, 14995),
  (21537, 22634, 15762),
  (22635, 23801, 16569),
  (23802, 25033, 17424),
  (25034, 26333, 18327),
  (26334, 27715, 19281),
  (27716, 29174, 20294),
  (29175, 30717, 21364),
  (30718, 32350, 22495),
  (32351, 35263, 23869),
  (35264, 38446, 26020),
  (38447, 41391, 28292),
  (41392, 42541, 29073),
  (42542, 43671, 29841),
  (43672, 44833, 30635),
  (44834, 46027, 31452),
  (46028, 47249, 32288),
  (47250, 48201, 32934),
  (48202, 49171, 33596),
  (49172, 50166, 34275),
  (50167, 51178, 34967),
  (51179, 52215, 35675),
  (52216, 53281, 36398),
  (53282, 54373, 37142),
  (54374, 55493, 37906),
  (55494, 56627, 38685),
  (56628, 57793, 39477),
  (57794, 58986, 40290),
  (58987, 60211, 41123),
  (60212, 61457, 41977),
  (61458, 62743, 42849),
  (62744, 64060, 43746),
  (64061, 67621, 44996),
  (67622, 71392, 47499),
  (71393, 75374, 50149),
  (75375, 79582, 52947),
  (79583, 83487, 55823),
  (83488, 87583, 58563),
  (87584, 91885, 61438),
  (91886, 96414, 64459),
  (96415, 101151, 67635),
  (101152, 106141, 70962),
  (106142, 111382, 74465),
  (111383, 116887, 78141),
  (116888, 122667, 82005),
  (122668, 128743, 86061),
  (128744, 139444, 90971),
  (139445, 151037, 98532),
  (151038, 163057, 106647),
  (163058, 176048, 115137),
  (176049, 190066, 124310),
  (190067, 205208, 134210),
  (205209, 221566, 144907),
  (221567, 239251, 156462),
  (239252, 258340, 168951),
  (258341, 287261, 183670),
  (287262, 319423, 204234),
  (319424, 354577, 227012),
  (354578, 393587, 251994),
  (393588, 436897, 279722),
  (436898, 484973, 310503),
  (484974, 553144, 346882),
  (553145, 630879, 395641),
  (630880, 718920, 451150),
  (718921, 808306, 507256),
  (808307, 879582, 551993),
  (879583, 949526, 595878),
  (949527, 1000000, 627559)]

end A085265Moderate

namespace A085265Moderate

open A085265Sieve

open A085265.DyadicPrimeCount

def primeDeltas (j : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range 1415).filter (fun p => 2 < p ∧ p.Prime), 2*j/(p^2)



private def deltaPrimeTable : List ℕ := [
  3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
  131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
  211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
  293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383,
  389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467,
  479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577,
  587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661,
  673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769,
  773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877,
  881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983,
  991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087,
  1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193,
  1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297,
  1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409]

/-- Compute the bounded prime set once, independently of the interval endpoint. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem deltaPrimeList_ok :
    (List.range 1415).filter (fun p => decide (2 < p ∧ p.Prime)) = deltaPrimeTable := by
  decide +kernel

private theorem deltaPrimeTable_ok :
    (Finset.range 1415).filter (fun p => 2 < p ∧ p.Prime) = deltaPrimeTable.toFinset := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, ← deltaPrimeList_ok]
  simp

private theorem list_sum_delta (ps : List ℕ) (j : ℕ) (h : ps.Nodup) :
    (∑ p ∈ ps.toFinset, 2*j/(p^2)) = (ps.map fun p => 2*j/(p^2)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hp,hs⟩ := List.nodup_cons.mp h
    have hn : p ∉ ps.toFinset := by simpa using hp
    rw [List.toFinset_cons, Finset.sum_insert hn, ih hs, List.map_cons, List.sum_cons]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem deltaPrimeTable_nodup : deltaPrimeTable.Nodup := by decide +kernel

private theorem primeDeltas_list (j : ℕ) :
    primeDeltas j = (deltaPrimeTable.map fun p => 2*j/(p^2)).sum := by
  unfold primeDeltas
  rw [deltaPrimeTable_ok, list_sum_delta _ _ deltaPrimeTable_nodup]




private theorem totalCostBound (j : ℕ) (hu : j ≤ 1000000) :
    (∑ p ∈ A085265Sieve.largePrimeSet (2*j+1), (2*j/(p^2)+1)) ≤
      oddPrimeCount (2*j+1) + primeDeltas j := by
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
  change (∑ p ∈ P, (2*j/(p^2)+1)) ≤ P.card + primeDeltas j
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  omega

private theorem liftCount {x m e a b : ℕ}
    (hmx : m ≤ x) (hxm : x ≤ 2*m) (he : 0 < e) (hp : 2^e ≤ m+1)
    (hab : a+x/e ≤ b) (h : oddPrimeCount m ≤ a) : oddPrimeCount x ≤ b :=
  (interval m x e hmx hxm he hp).trans ((Nat.add_le_add_right h _).trans hab)

private def endpointCostOK (c : ℕ × ℕ × ℤ) : Prop :=
  ((∑ p ∈ A085265Sieve.largePrimeSet (2*c.2.1+1), (2*c.2.1/(p^2)+1)) : ℕ) ≤ c.2.2

private theorem endpointCost_of_parts {j a d : ℕ} {c : ℤ}
    (hj : j ≤ 1000000) (hp : oddPrimeCount (2*j+1) ≤ a)
    (hd : (deltaPrimeTable.map (fun p => 2*j/(p^2))).sum = d)
    (hc : ((a+d : ℕ) : ℤ) ≤ c) :
    ((∑ p ∈ A085265Sieve.largePrimeSet (2*j+1), (2*j/(p^2)+1)) : ℕ) ≤ c := by
  have h := totalCostBound j hj
  rw [primeDeltas_list, hd] at h
  exact (Int.ofNat_le.mpr (h.trans (Nat.add_le_add_right hp d))).trans hc


set_option maxRecDepth 20000 in
private theorem endpointCost300 : endpointCostOK (300, 307, 227) := by
  have h615 := base_615
  exact endpointCost_of_parts (j := 307) (a := 111) (d := 116)
    (by decide) h615 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost308 : endpointCostOK (308, 314, 231) := by
  have h629 := base_629
  exact endpointCost_of_parts (j := 314) (a := 113) (d := 118)
    (by decide) h629 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost315 : endpointCostOK (315, 323, 238) := by
  have h647 := base_647
  exact endpointCost_of_parts (j := 323) (a := 117) (d := 121)
    (by decide) h647 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost324 : endpointCostOK (324, 332, 244) := by
  have h665 := base_665
  exact endpointCost_of_parts (j := 332) (a := 120) (d := 124)
    (by decide) h665 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost333 : endpointCostOK (333, 341, 251) := by
  have h683 := base_683
  exact endpointCost_of_parts (j := 341) (a := 123) (d := 128)
    (by decide) h683 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost342 : endpointCostOK (342, 355, 259) := by
  have h711 := base_711
  exact endpointCost_of_parts (j := 355) (a := 126) (d := 133)
    (by decide) h711 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost356 : endpointCostOK (356, 368, 269) := by
  have h737 := base_737
  exact endpointCost_of_parts (j := 368) (a := 129) (d := 140)
    (by decide) h737 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost369 : endpointCostOK (369, 385, 280) := by
  have h771 := base_771
  exact endpointCost_of_parts (j := 385) (a := 135) (d := 145)
    (by decide) h771 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost386 : endpointCostOK (386, 409, 293) := by
  have h819 := base_819
  exact endpointCost_of_parts (j := 409) (a := 140) (d := 153)
    (by decide) h819 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost410 : endpointCostOK (410, 430, 312) := by
  have h861 := base_861
  exact endpointCost_of_parts (j := 430) (a := 148) (d := 164)
    (by decide) h861 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost431 : endpointCostOK (431, 454, 327) := by
  have h909 := base_909
  exact endpointCost_of_parts (j := 454) (a := 154) (d := 173)
    (by decide) h909 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost455 : endpointCostOK (455, 484, 347) := by
  have h969 := base_969
  exact endpointCost_of_parts (j := 484) (a := 162) (d := 185)
    (by decide) h969 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost485 : endpointCostOK (485, 517, 371) := by
  have h1035 := base_1035
  exact endpointCost_of_parts (j := 517) (a := 173) (d := 198)
    (by decide) h1035 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost518 : endpointCostOK (518, 550, 396) := by
  have h1101 := base_1101
  exact endpointCost_of_parts (j := 550) (a := 183) (d := 213)
    (by decide) h1101 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost551 : endpointCostOK (551, 592, 422) := by
  have h1185 := base_1185
  exact endpointCost_of_parts (j := 592) (a := 193) (d := 229)
    (by decide) h1185 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost593 : endpointCostOK (593, 643, 454) := by
  have h1287 := base_1287
  exact endpointCost_of_parts (j := 643) (a := 207) (d := 247)
    (by decide) h1287 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost644 : endpointCostOK (644, 710, 494) := by
  have h1421 := base_1421
  exact endpointCost_of_parts (j := 710) (a := 222) (d := 272)
    (by decide) h1421 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost711 : endpointCostOK (711, 782, 546) := by
  have h1565 := base_1565
  exact endpointCost_of_parts (j := 782) (a := 245) (d := 301)
    (by decide) h1565 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost783 : endpointCostOK (783, 865, 605) := by
  have h1731 := base_1731
  exact endpointCost_of_parts (j := 865) (a := 268) (d := 337)
    (by decide) h1731 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost866 : endpointCostOK (866, 964, 669) := by
  have h1929 := base_1929
  exact endpointCost_of_parts (j := 964) (a := 292) (d := 377)
    (by decide) h1929 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost965 : endpointCostOK (965, 1082, 747) := by
  have h2165 := base_2165
  exact endpointCost_of_parts (j := 1082) (a := 325) (d := 422)
    (by decide) h2165 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1083 : endpointCostOK (1083, 1228, 842) := by
  have h2457 := base_2457
  exact endpointCost_of_parts (j := 1228) (a := 362) (d := 480)
    (by decide) h2457 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1229 : endpointCostOK (1229, 1400, 957) := by
  have h2801 := base_2801
  exact endpointCost_of_parts (j := 1400) (a := 407) (d := 550)
    (by decide) h2801 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1401 : endpointCostOK (1401, 1624, 1093) := by
  have h3249 := base_3249
  exact endpointCost_of_parts (j := 1624) (a := 456) (d := 637)
    (by decide) h3249 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1625 : endpointCostOK (1625, 1885, 1268) := by
  have h3771 := base_3771
  exact endpointCost_of_parts (j := 1885) (a := 524) (d := 744)
    (by decide) h3771 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1886 : endpointCostOK (1886, 2213, 1477) := by
  have h4427 := base_4427
  exact endpointCost_of_parts (j := 2213) (a := 601) (d := 876)
    (by decide) h4427 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost2214 : endpointCostOK (2214, 2501, 1658) := by
  have h5003 := base_5003
  exact endpointCost_of_parts (j := 2501) (a := 669) (d := 989)
    (by decide) h5003 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost2502 : endpointCostOK (2502, 2810, 1852) := by
  have h5621 := base_5621
  exact endpointCost_of_parts (j := 2810) (a := 737) (d := 1115)
    (by decide) h5621 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost2811 : endpointCostOK (2811, 3175, 2085) := by
  have h6351 := base_6351
  exact endpointCost_of_parts (j := 3175) (a := 825) (d := 1260)
    (by decide) h6351 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost3176 : endpointCostOK (3176, 3613, 2359) := by
  have h7227 := base_7227
  exact endpointCost_of_parts (j := 3613) (a := 922) (d := 1437)
    (by decide) h7227 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost3614 : endpointCostOK (3614, 4153, 2693) := by
  have h8307 := base_8307
  exact endpointCost_of_parts (j := 4153) (a := 1041) (d := 1652)
    (by decide) h8307 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost4154 : endpointCostOK (4154, 4805, 3100) := by
  have h9611 := base_9611
  exact endpointCost_of_parts (j := 4805) (a := 1184) (d := 1916)
    (by decide) h9611 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost4806 : endpointCostOK (4806, 5021, 3506) := by
  have h5022 := base_5022
  have h10043 : oddPrimeCount 10043 ≤ 1509 :=
    liftCount (m := 5022) (e := 12) (a := 672) (by decide) (by decide) (by decide) (by decide) (by decide) h5022
  exact endpointCost_of_parts (j := 5021) (a := 1509) (d := 1997)
    (by decide) h10043 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5022 : endpointCostOK (5022, 5255, 3667) := by
  have h5256 := base_5256
  have h10511 : oddPrimeCount 10511 ≤ 1572 :=
    liftCount (m := 5256) (e := 12) (a := 696) (by decide) (by decide) (by decide) (by decide) (by decide) h5256
  exact endpointCost_of_parts (j := 5255) (a := 1572) (d := 2095)
    (by decide) h10511 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5256 : endpointCostOK (5256, 5503, 3839) := by
  have h5504 := base_5504
  have h11007 : oddPrimeCount 11007 ≤ 1643 :=
    liftCount (m := 5504) (e := 12) (a := 726) (by decide) (by decide) (by decide) (by decide) (by decide) h5504
  exact endpointCost_of_parts (j := 5503) (a := 1643) (d := 2196)
    (by decide) h11007 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5504 : endpointCostOK (5504, 5770, 4022) := by
  have h5771 := base_5771
  have h11541 : oddPrimeCount 11541 ≤ 1717 :=
    liftCount (m := 5771) (e := 12) (a := 756) (by decide) (by decide) (by decide) (by decide) (by decide) h5771
  exact endpointCost_of_parts (j := 5770) (a := 1717) (d := 2305)
    (by decide) h11541 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5771 : endpointCostOK (5771, 6058, 4218) := by
  have h6059 := base_6059
  have h12117 : oddPrimeCount 12117 ≤ 1798 :=
    liftCount (m := 6059) (e := 12) (a := 789) (by decide) (by decide) (by decide) (by decide) (by decide) h6059
  exact endpointCost_of_parts (j := 6058) (a := 1798) (d := 2420)
    (by decide) h12117 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost6059 : endpointCostOK (6059, 6358, 4428) := by
  have h6359 := base_6359
  have h12717 : oddPrimeCount 12717 ≤ 1886 :=
    liftCount (m := 6359) (e := 12) (a := 827) (by decide) (by decide) (by decide) (by decide) (by decide) h6359
  exact endpointCost_of_parts (j := 6358) (a := 1886) (d := 2542)
    (by decide) h12717 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost6359 : endpointCostOK (6359, 6694, 4652) := by
  have h6695 := base_6695
  have h13389 : oddPrimeCount 13389 ≤ 1977 :=
    liftCount (m := 6695) (e := 12) (a := 862) (by decide) (by decide) (by decide) (by decide) (by decide) h6695
  exact endpointCost_of_parts (j := 6694) (a := 1977) (d := 2675)
    (by decide) h13389 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost6695 : endpointCostOK (6695, 7046, 4897) := by
  have h7047 := base_7047
  have h14093 : oddPrimeCount 14093 ≤ 2079 :=
    liftCount (m := 7047) (e := 12) (a := 905) (by decide) (by decide) (by decide) (by decide) (by decide) h7047
  exact endpointCost_of_parts (j := 7046) (a := 2079) (d := 2818)
    (by decide) h14093 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost7047 : endpointCostOK (7047, 7447, 5160) := by
  have h7448 := base_7448
  have h14895 : oddPrimeCount 14895 ≤ 2182 :=
    liftCount (m := 7448) (e := 12) (a := 941) (by decide) (by decide) (by decide) (by decide) (by decide) h7448
  exact endpointCost_of_parts (j := 7447) (a := 2182) (d := 2978)
    (by decide) h14895 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost7448 : endpointCostOK (7448, 7874, 5454) := by
  have h7875 := base_7875
  have h15749 : oddPrimeCount 15749 ≤ 2305 :=
    liftCount (m := 7875) (e := 12) (a := 993) (by decide) (by decide) (by decide) (by decide) (by decide) h7875
  exact endpointCost_of_parts (j := 7874) (a := 2305) (d := 3149)
    (by decide) h15749 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost7875 : endpointCostOK (7875, 8546, 5800) := by
  have h8547 := base_8547
  have h17093 : oddPrimeCount 17093 ≤ 2379 :=
    liftCount (m := 8547) (e := 13) (a := 1065) (by decide) (by decide) (by decide) (by decide) (by decide) h8547
  exact endpointCost_of_parts (j := 8546) (a := 2379) (d := 3421)
    (by decide) h17093 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost8547 : endpointCostOK (8547, 9291, 6298) := by
  have h9292 := base_9292
  have h18583 : oddPrimeCount 18583 ≤ 2578 :=
    liftCount (m := 9292) (e := 13) (a := 1149) (by decide) (by decide) (by decide) (by decide) (by decide) h9292
  exact endpointCost_of_parts (j := 9291) (a := 2578) (d := 3720)
    (by decide) h18583 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost9292 : endpointCostOK (9292, 9999, 6771) := by
  have h10000 := base_10000
  have h19999 : oddPrimeCount 19999 ≤ 2766 :=
    liftCount (m := 10000) (e := 13) (a := 1228) (by decide) (by decide) (by decide) (by decide) (by decide) h10000
  exact endpointCost_of_parts (j := 9999) (a := 2766) (d := 4005)
    (by decide) h19999 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost10000 : endpointCostOK (10000, 10353, 7292) := by
  have h5177 := base_5177
  have h10354 : oddPrimeCount 10354 ≤ 1550 :=
    liftCount (m := 5177) (e := 12) (a := 688) (by decide) (by decide) (by decide) (by decide) (by decide) h5177
  have h20707 : oddPrimeCount 20707 ≤ 3142 :=
    liftCount (m := 10354) (e := 13) (a := 1550) (by decide) (by decide) (by decide) (by decide) (by decide) h10354
  exact endpointCost_of_parts (j := 10353) (a := 3142) (d := 4150)
    (by decide) h20707 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost10354 : endpointCostOK (10354, 10730, 7551) := by
  have h5366 := base_5366
  have h10731 : oddPrimeCount 10731 ≤ 1601 :=
    liftCount (m := 5366) (e := 12) (a := 707) (by decide) (by decide) (by decide) (by decide) (by decide) h5366
  have h21461 : oddPrimeCount 21461 ≤ 3251 :=
    liftCount (m := 10731) (e := 13) (a := 1601) (by decide) (by decide) (by decide) (by decide) (by decide) h10731
  exact endpointCost_of_parts (j := 10730) (a := 3251) (d := 4300)
    (by decide) h21461 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost10731 : endpointCostOK (10731, 11120, 7826) := by
  have h5561 := base_5561
  have h11121 : oddPrimeCount 11121 ≤ 1658 :=
    liftCount (m := 5561) (e := 12) (a := 732) (by decide) (by decide) (by decide) (by decide) (by decide) h5561
  have h22241 : oddPrimeCount 22241 ≤ 3368 :=
    liftCount (m := 11121) (e := 13) (a := 1658) (by decide) (by decide) (by decide) (by decide) (by decide) h11121
  exact endpointCost_of_parts (j := 11120) (a := 3368) (d := 4458)
    (by decide) h22241 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost11121 : endpointCostOK (11121, 11529, 8112) := by
  have h5765 := base_5765
  have h11530 : oddPrimeCount 11530 ≤ 1716 :=
    liftCount (m := 5765) (e := 12) (a := 756) (by decide) (by decide) (by decide) (by decide) (by decide) h5765
  have h23059 : oddPrimeCount 23059 ≤ 3489 :=
    liftCount (m := 11530) (e := 13) (a := 1716) (by decide) (by decide) (by decide) (by decide) (by decide) h11530
  exact endpointCost_of_parts (j := 11529) (a := 3489) (d := 4623)
    (by decide) h23059 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost11530 : endpointCostOK (11530, 11959, 8412) := by
  have h5980 := base_5980
  have h11960 : oddPrimeCount 11960 ≤ 1776 :=
    liftCount (m := 5980) (e := 12) (a := 780) (by decide) (by decide) (by decide) (by decide) (by decide) h5980
  have h23919 : oddPrimeCount 23919 ≤ 3616 :=
    liftCount (m := 11960) (e := 13) (a := 1776) (by decide) (by decide) (by decide) (by decide) (by decide) h11960
  exact endpointCost_of_parts (j := 11959) (a := 3616) (d := 4796)
    (by decide) h23919 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost11960 : endpointCostOK (11960, 12415, 8728) := by
  have h6208 := base_6208
  have h12416 : oddPrimeCount 12416 ≤ 1840 :=
    liftCount (m := 6208) (e := 12) (a := 806) (by decide) (by decide) (by decide) (by decide) (by decide) h6208
  have h24831 : oddPrimeCount 24831 ≤ 3750 :=
    liftCount (m := 12416) (e := 13) (a := 1840) (by decide) (by decide) (by decide) (by decide) (by decide) h12416
  exact endpointCost_of_parts (j := 12415) (a := 3750) (d := 4978)
    (by decide) h24831 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost12416 : endpointCostOK (12416, 12887, 9061) := by
  have h6444 := base_6444
  have h12888 : oddPrimeCount 12888 ≤ 1909 :=
    liftCount (m := 6444) (e := 12) (a := 835) (by decide) (by decide) (by decide) (by decide) (by decide) h6444
  have h25775 : oddPrimeCount 25775 ≤ 3891 :=
    liftCount (m := 12888) (e := 13) (a := 1909) (by decide) (by decide) (by decide) (by decide) (by decide) h12888
  exact endpointCost_of_parts (j := 12887) (a := 3891) (d := 5170)
    (by decide) h25775 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost12888 : endpointCostOK (12888, 13387, 9407) := by
  have h6694 := base_6694
  have h13388 : oddPrimeCount 13388 ≤ 1977 :=
    liftCount (m := 6694) (e := 12) (a := 862) (by decide) (by decide) (by decide) (by decide) (by decide) h6694
  have h26775 : oddPrimeCount 26775 ≤ 4036 :=
    liftCount (m := 13388) (e := 13) (a := 1977) (by decide) (by decide) (by decide) (by decide) (by decide) h13388
  exact endpointCost_of_parts (j := 13387) (a := 4036) (d := 5371)
    (by decide) h26775 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost13388 : endpointCostOK (13388, 13909, 9771) := by
  have h6955 := base_6955
  have h13910 : oddPrimeCount 13910 ≤ 2050 :=
    liftCount (m := 6955) (e := 12) (a := 891) (by decide) (by decide) (by decide) (by decide) (by decide) h6955
  have h27819 : oddPrimeCount 27819 ≤ 4190 :=
    liftCount (m := 13910) (e := 13) (a := 2050) (by decide) (by decide) (by decide) (by decide) (by decide) h13910
  exact endpointCost_of_parts (j := 13909) (a := 4190) (d := 5581)
    (by decide) h27819 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost13910 : endpointCostOK (13910, 14455, 10155) := by
  have h7228 := base_7228
  have h14456 : oddPrimeCount 14456 ≤ 2126 :=
    liftCount (m := 7228) (e := 12) (a := 922) (by decide) (by decide) (by decide) (by decide) (by decide) h7228
  have h28911 : oddPrimeCount 28911 ≤ 4350 :=
    liftCount (m := 14456) (e := 13) (a := 2126) (by decide) (by decide) (by decide) (by decide) (by decide) h14456
  exact endpointCost_of_parts (j := 14455) (a := 4350) (d := 5805)
    (by decide) h28911 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost14456 : endpointCostOK (14456, 15045, 10557) := by
  have h7523 := base_7523
  have h15046 : oddPrimeCount 15046 ≤ 2205 :=
    liftCount (m := 7523) (e := 12) (a := 952) (by decide) (by decide) (by decide) (by decide) (by decide) h7523
  have h30091 : oddPrimeCount 30091 ≤ 4519 :=
    liftCount (m := 15046) (e := 13) (a := 2205) (by decide) (by decide) (by decide) (by decide) (by decide) h15046
  exact endpointCost_of_parts (j := 15045) (a := 4519) (d := 6038)
    (by decide) h30091 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost15046 : endpointCostOK (15046, 15657, 10986) := by
  have h7829 := base_7829
  have h15658 : oddPrimeCount 15658 ≤ 2293 :=
    liftCount (m := 7829) (e := 12) (a := 989) (by decide) (by decide) (by decide) (by decide) (by decide) h7829
  have h31315 : oddPrimeCount 31315 ≤ 4701 :=
    liftCount (m := 15658) (e := 13) (a := 2293) (by decide) (by decide) (by decide) (by decide) (by decide) h15658
  exact endpointCost_of_parts (j := 15657) (a := 4701) (d := 6285)
    (by decide) h31315 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost15658 : endpointCostOK (15658, 16838, 11516) := by
  have h8420 := base_8420
  have h16839 : oddPrimeCount 16839 ≤ 2346 :=
    liftCount (m := 8420) (e := 13) (a := 1051) (by decide) (by decide) (by decide) (by decide) (by decide) h8420
  have h33677 : oddPrimeCount 33677 ≤ 4751 :=
    liftCount (m := 16839) (e := 14) (a := 2346) (by decide) (by decide) (by decide) (by decide) (by decide) h16839
  exact endpointCost_of_parts (j := 16838) (a := 4751) (d := 6765)
    (by decide) h33677 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost16839 : endpointCostOK (16839, 18121, 12386) := by
  have h9061 := base_9061
  have h18122 : oddPrimeCount 18122 ≤ 2519 :=
    liftCount (m := 9061) (e := 13) (a := 1125) (by decide) (by decide) (by decide) (by decide) (by decide) h9061
  have h36243 : oddPrimeCount 36243 ≤ 5107 :=
    liftCount (m := 18122) (e := 14) (a := 2519) (by decide) (by decide) (by decide) (by decide) (by decide) h18122
  exact endpointCost_of_parts (j := 18121) (a := 5107) (d := 7279)
    (by decide) h36243 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost18122 : endpointCostOK (18122, 19507, 13329) := by
  have h9754 := base_9754
  have h19508 : oddPrimeCount 19508 ≤ 2702 :=
    liftCount (m := 9754) (e := 13) (a := 1202) (by decide) (by decide) (by decide) (by decide) (by decide) h9754
  have h39015 : oddPrimeCount 39015 ≤ 5488 :=
    liftCount (m := 19508) (e := 14) (a := 2702) (by decide) (by decide) (by decide) (by decide) (by decide) h19508
  exact endpointCost_of_parts (j := 19507) (a := 5488) (d := 7841)
    (by decide) h39015 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost19508 : endpointCostOK (19508, 20487, 14275) := by
  have h5122 := base_5122
  have h10244 : oddPrimeCount 10244 ≤ 1537 :=
    liftCount (m := 5122) (e := 12) (a := 684) (by decide) (by decide) (by decide) (by decide) (by decide) h5122
  have h20488 : oddPrimeCount 20488 ≤ 3113 :=
    liftCount (m := 10244) (e := 13) (a := 1537) (by decide) (by decide) (by decide) (by decide) (by decide) h10244
  have h40975 : oddPrimeCount 40975 ≤ 6039 :=
    liftCount (m := 20488) (e := 14) (a := 3113) (by decide) (by decide) (by decide) (by decide) (by decide) h20488
  exact endpointCost_of_parts (j := 20487) (a := 6039) (d := 8236)
    (by decide) h40975 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost20488 : endpointCostOK (20488, 21536, 14995) := by
  have h5385 := base_5385
  have h10769 : oddPrimeCount 10769 ≤ 1605 :=
    liftCount (m := 5385) (e := 12) (a := 708) (by decide) (by decide) (by decide) (by decide) (by decide) h5385
  have h21537 : oddPrimeCount 21537 ≤ 3261 :=
    liftCount (m := 10769) (e := 13) (a := 1605) (by decide) (by decide) (by decide) (by decide) (by decide) h10769
  have h43073 : oddPrimeCount 43073 ≤ 6337 :=
    liftCount (m := 21537) (e := 14) (a := 3261) (by decide) (by decide) (by decide) (by decide) (by decide) h21537
  exact endpointCost_of_parts (j := 21536) (a := 6337) (d := 8658)
    (by decide) h43073 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost21537 : endpointCostOK (21537, 22634, 15762) := by
  have h5659 := base_5659
  have h11318 : oddPrimeCount 11318 ≤ 1688 :=
    liftCount (m := 5659) (e := 12) (a := 745) (by decide) (by decide) (by decide) (by decide) (by decide) h5659
  have h22635 : oddPrimeCount 22635 ≤ 3429 :=
    liftCount (m := 11318) (e := 13) (a := 1688) (by decide) (by decide) (by decide) (by decide) (by decide) h11318
  have h45269 : oddPrimeCount 45269 ≤ 6662 :=
    liftCount (m := 22635) (e := 14) (a := 3429) (by decide) (by decide) (by decide) (by decide) (by decide) h22635
  exact endpointCost_of_parts (j := 22634) (a := 6662) (d := 9100)
    (by decide) h45269 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost22635 : endpointCostOK (22635, 23801, 16569) := by
  have h5951 := base_5951
  have h11901 : oddPrimeCount 11901 ≤ 1770 :=
    liftCount (m := 5951) (e := 12) (a := 779) (by decide) (by decide) (by decide) (by decide) (by decide) h5951
  have h23802 : oddPrimeCount 23802 ≤ 3600 :=
    liftCount (m := 11901) (e := 13) (a := 1770) (by decide) (by decide) (by decide) (by decide) (by decide) h11901
  have h47603 : oddPrimeCount 47603 ≤ 7000 :=
    liftCount (m := 23802) (e := 14) (a := 3600) (by decide) (by decide) (by decide) (by decide) (by decide) h23802
  exact endpointCost_of_parts (j := 23801) (a := 7000) (d := 9569)
    (by decide) h47603 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost23802 : endpointCostOK (23802, 25033, 17424) := by
  have h6259 := base_6259
  have h12517 : oddPrimeCount 12517 ≤ 1855 :=
    liftCount (m := 6259) (e := 12) (a := 812) (by decide) (by decide) (by decide) (by decide) (by decide) h6259
  have h25034 : oddPrimeCount 25034 ≤ 3780 :=
    liftCount (m := 12517) (e := 13) (a := 1855) (by decide) (by decide) (by decide) (by decide) (by decide) h12517
  have h50067 : oddPrimeCount 50067 ≤ 7356 :=
    liftCount (m := 25034) (e := 14) (a := 3780) (by decide) (by decide) (by decide) (by decide) (by decide) h25034
  exact endpointCost_of_parts (j := 25033) (a := 7356) (d := 10068)
    (by decide) h50067 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost25034 : endpointCostOK (25034, 26333, 18327) := by
  have h6584 := base_6584
  have h13167 : oddPrimeCount 13167 ≤ 1948 :=
    liftCount (m := 6584) (e := 12) (a := 851) (by decide) (by decide) (by decide) (by decide) (by decide) h6584
  have h26334 : oddPrimeCount 26334 ≤ 3973 :=
    liftCount (m := 13167) (e := 13) (a := 1948) (by decide) (by decide) (by decide) (by decide) (by decide) h13167
  have h52667 : oddPrimeCount 52667 ≤ 7735 :=
    liftCount (m := 26334) (e := 14) (a := 3973) (by decide) (by decide) (by decide) (by decide) (by decide) h26334
  exact endpointCost_of_parts (j := 26333) (a := 7735) (d := 10592)
    (by decide) h52667 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost26334 : endpointCostOK (26334, 27715, 19281) := by
  have h6929 := base_6929
  have h13858 : oddPrimeCount 13858 ≤ 2043 :=
    liftCount (m := 6929) (e := 12) (a := 889) (by decide) (by decide) (by decide) (by decide) (by decide) h6929
  have h27716 : oddPrimeCount 27716 ≤ 4175 :=
    liftCount (m := 13858) (e := 13) (a := 2043) (by decide) (by decide) (by decide) (by decide) (by decide) h13858
  have h55431 : oddPrimeCount 55431 ≤ 8134 :=
    liftCount (m := 27716) (e := 14) (a := 4175) (by decide) (by decide) (by decide) (by decide) (by decide) h27716
  exact endpointCost_of_parts (j := 27715) (a := 8134) (d := 11147)
    (by decide) h55431 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost27716 : endpointCostOK (27716, 29174, 20294) := by
  have h7294 := base_7294
  have h14588 : oddPrimeCount 14588 ≤ 2143 :=
    liftCount (m := 7294) (e := 12) (a := 928) (by decide) (by decide) (by decide) (by decide) (by decide) h7294
  have h29175 : oddPrimeCount 29175 ≤ 4387 :=
    liftCount (m := 14588) (e := 13) (a := 2143) (by decide) (by decide) (by decide) (by decide) (by decide) h14588
  have h58349 : oddPrimeCount 58349 ≤ 8554 :=
    liftCount (m := 29175) (e := 14) (a := 4387) (by decide) (by decide) (by decide) (by decide) (by decide) h29175
  exact endpointCost_of_parts (j := 29174) (a := 8554) (d := 11740)
    (by decide) h58349 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost29175 : endpointCostOK (29175, 30717, 21364) := by
  have h7680 := base_7680
  have h15359 : oddPrimeCount 15359 ≤ 2252 :=
    liftCount (m := 7680) (e := 12) (a := 972) (by decide) (by decide) (by decide) (by decide) (by decide) h7680
  have h30718 : oddPrimeCount 30718 ≤ 4614 :=
    liftCount (m := 15359) (e := 13) (a := 2252) (by decide) (by decide) (by decide) (by decide) (by decide) h15359
  have h61435 : oddPrimeCount 61435 ≤ 9002 :=
    liftCount (m := 30718) (e := 14) (a := 4614) (by decide) (by decide) (by decide) (by decide) (by decide) h30718
  exact endpointCost_of_parts (j := 30717) (a := 9002) (d := 12362)
    (by decide) h61435 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost30718 : endpointCostOK (30718, 32350, 22495) := by
  have h8088 := base_8088
  have h16176 : oddPrimeCount 16176 ≤ 2363 :=
    liftCount (m := 8088) (e := 12) (a := 1015) (by decide) (by decide) (by decide) (by decide) (by decide) h8088
  have h32351 : oddPrimeCount 32351 ≤ 4851 :=
    liftCount (m := 16176) (e := 13) (a := 2363) (by decide) (by decide) (by decide) (by decide) (by decide) h16176
  have h64701 : oddPrimeCount 64701 ≤ 9472 :=
    liftCount (m := 32351) (e := 14) (a := 4851) (by decide) (by decide) (by decide) (by decide) (by decide) h32351
  exact endpointCost_of_parts (j := 32350) (a := 9472) (d := 13023)
    (by decide) h64701 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost32351 : endpointCostOK (32351, 35263, 23869) := by
  have h8816 := base_8816
  have h17632 : oddPrimeCount 17632 ≤ 2452 :=
    liftCount (m := 8816) (e := 13) (a := 1096) (by decide) (by decide) (by decide) (by decide) (by decide) h8816
  have h35264 : oddPrimeCount 35264 ≤ 4970 :=
    liftCount (m := 17632) (e := 14) (a := 2452) (by decide) (by decide) (by decide) (by decide) (by decide) h17632
  have h70527 : oddPrimeCount 70527 ≤ 9671 :=
    liftCount (m := 35264) (e := 15) (a := 4970) (by decide) (by decide) (by decide) (by decide) (by decide) h35264
  exact endpointCost_of_parts (j := 35263) (a := 9671) (d := 14198)
    (by decide) h70527 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost35264 : endpointCostOK (35264, 38446, 26020) := by
  have h9612 := base_9612
  have h19224 : oddPrimeCount 19224 ≤ 2662 :=
    liftCount (m := 9612) (e := 13) (a := 1184) (by decide) (by decide) (by decide) (by decide) (by decide) h9612
  have h38447 : oddPrimeCount 38447 ≤ 5408 :=
    liftCount (m := 19224) (e := 14) (a := 2662) (by decide) (by decide) (by decide) (by decide) (by decide) h19224
  have h76893 : oddPrimeCount 76893 ≤ 10534 :=
    liftCount (m := 38447) (e := 15) (a := 5408) (by decide) (by decide) (by decide) (by decide) (by decide) h38447
  exact endpointCost_of_parts (j := 38446) (a := 10534) (d := 15486)
    (by decide) h76893 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost38447 : endpointCostOK (38447, 41391, 28292) := by
  have h5174 := base_5174
  have h10348 : oddPrimeCount 10348 ≤ 1550 :=
    liftCount (m := 5174) (e := 12) (a := 688) (by decide) (by decide) (by decide) (by decide) (by decide) h5174
  have h20696 : oddPrimeCount 20696 ≤ 3142 :=
    liftCount (m := 10348) (e := 13) (a := 1550) (by decide) (by decide) (by decide) (by decide) (by decide) h10348
  have h41392 : oddPrimeCount 41392 ≤ 6098 :=
    liftCount (m := 20696) (e := 14) (a := 3142) (by decide) (by decide) (by decide) (by decide) (by decide) h20696
  have h82783 : oddPrimeCount 82783 ≤ 11616 :=
    liftCount (m := 41392) (e := 15) (a := 6098) (by decide) (by decide) (by decide) (by decide) (by decide) h41392
  exact endpointCost_of_parts (j := 41391) (a := 11616) (d := 16676)
    (by decide) h82783 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost41392 : endpointCostOK (41392, 42541, 29073) := by
  have h5318 := base_5318
  have h10636 : oddPrimeCount 10636 ≤ 1589 :=
    liftCount (m := 5318) (e := 12) (a := 703) (by decide) (by decide) (by decide) (by decide) (by decide) h5318
  have h21271 : oddPrimeCount 21271 ≤ 3225 :=
    liftCount (m := 10636) (e := 13) (a := 1589) (by decide) (by decide) (by decide) (by decide) (by decide) h10636
  have h42542 : oddPrimeCount 42542 ≤ 6263 :=
    liftCount (m := 21271) (e := 14) (a := 3225) (by decide) (by decide) (by decide) (by decide) (by decide) h21271
  have h85083 : oddPrimeCount 85083 ≤ 11935 :=
    liftCount (m := 42542) (e := 15) (a := 6263) (by decide) (by decide) (by decide) (by decide) (by decide) h42542
  exact endpointCost_of_parts (j := 42541) (a := 11935) (d := 17138)
    (by decide) h85083 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost42542 : endpointCostOK (42542, 43671, 29841) := by
  have h5459 := base_5459
  have h10918 : oddPrimeCount 10918 ≤ 1629 :=
    liftCount (m := 5459) (e := 12) (a := 720) (by decide) (by decide) (by decide) (by decide) (by decide) h5459
  have h21836 : oddPrimeCount 21836 ≤ 3308 :=
    liftCount (m := 10918) (e := 13) (a := 1629) (by decide) (by decide) (by decide) (by decide) (by decide) h10918
  have h43672 : oddPrimeCount 43672 ≤ 6427 :=
    liftCount (m := 21836) (e := 14) (a := 3308) (by decide) (by decide) (by decide) (by decide) (by decide) h21836
  have h87343 : oddPrimeCount 87343 ≤ 12249 :=
    liftCount (m := 43672) (e := 15) (a := 6427) (by decide) (by decide) (by decide) (by decide) (by decide) h43672
  exact endpointCost_of_parts (j := 43671) (a := 12249) (d := 17592)
    (by decide) h87343 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost43672 : endpointCostOK (43672, 44833, 30635) := by
  have h5605 := base_5605
  have h11209 : oddPrimeCount 11209 ≤ 1671 :=
    liftCount (m := 5605) (e := 12) (a := 737) (by decide) (by decide) (by decide) (by decide) (by decide) h5605
  have h22417 : oddPrimeCount 22417 ≤ 3395 :=
    liftCount (m := 11209) (e := 13) (a := 1671) (by decide) (by decide) (by decide) (by decide) (by decide) h11209
  have h44834 : oddPrimeCount 44834 ≤ 6597 :=
    liftCount (m := 22417) (e := 14) (a := 3395) (by decide) (by decide) (by decide) (by decide) (by decide) h22417
  have h89667 : oddPrimeCount 89667 ≤ 12574 :=
    liftCount (m := 44834) (e := 15) (a := 6597) (by decide) (by decide) (by decide) (by decide) (by decide) h44834
  exact endpointCost_of_parts (j := 44833) (a := 12574) (d := 18061)
    (by decide) h89667 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost44834 : endpointCostOK (44834, 46027, 31452) := by
  have h5754 := base_5754
  have h11507 : oddPrimeCount 11507 ≤ 1715 :=
    liftCount (m := 5754) (e := 12) (a := 756) (by decide) (by decide) (by decide) (by decide) (by decide) h5754
  have h23014 : oddPrimeCount 23014 ≤ 3485 :=
    liftCount (m := 11507) (e := 13) (a := 1715) (by decide) (by decide) (by decide) (by decide) (by decide) h11507
  have h46028 : oddPrimeCount 46028 ≤ 6772 :=
    liftCount (m := 23014) (e := 14) (a := 3485) (by decide) (by decide) (by decide) (by decide) (by decide) h23014
  have h92055 : oddPrimeCount 92055 ≤ 12909 :=
    liftCount (m := 46028) (e := 15) (a := 6772) (by decide) (by decide) (by decide) (by decide) (by decide) h46028
  exact endpointCost_of_parts (j := 46027) (a := 12909) (d := 18543)
    (by decide) h92055 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost46028 : endpointCostOK (46028, 47249, 32288) := by
  have h5907 := base_5907
  have h11813 : oddPrimeCount 11813 ≤ 1760 :=
    liftCount (m := 5907) (e := 12) (a := 776) (by decide) (by decide) (by decide) (by decide) (by decide) h5907
  have h23625 : oddPrimeCount 23625 ≤ 3577 :=
    liftCount (m := 11813) (e := 13) (a := 1760) (by decide) (by decide) (by decide) (by decide) (by decide) h11813
  have h47250 : oddPrimeCount 47250 ≤ 6952 :=
    liftCount (m := 23625) (e := 14) (a := 3577) (by decide) (by decide) (by decide) (by decide) (by decide) h23625
  have h94499 : oddPrimeCount 94499 ≤ 13252 :=
    liftCount (m := 47250) (e := 15) (a := 6952) (by decide) (by decide) (by decide) (by decide) (by decide) h47250
  exact endpointCost_of_parts (j := 47249) (a := 13252) (d := 19036)
    (by decide) h94499 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost47250 : endpointCostOK (47250, 48201, 32934) := by
  have h6026 := base_6026
  have h12051 : oddPrimeCount 12051 ≤ 1788 :=
    liftCount (m := 6026) (e := 12) (a := 784) (by decide) (by decide) (by decide) (by decide) (by decide) h6026
  have h24101 : oddPrimeCount 24101 ≤ 3642 :=
    liftCount (m := 12051) (e := 13) (a := 1788) (by decide) (by decide) (by decide) (by decide) (by decide) h12051
  have h48202 : oddPrimeCount 48202 ≤ 7085 :=
    liftCount (m := 24101) (e := 14) (a := 3642) (by decide) (by decide) (by decide) (by decide) (by decide) h24101
  have h96403 : oddPrimeCount 96403 ≤ 13511 :=
    liftCount (m := 48202) (e := 15) (a := 7085) (by decide) (by decide) (by decide) (by decide) (by decide) h48202
  exact endpointCost_of_parts (j := 48201) (a := 13511) (d := 19423)
    (by decide) h96403 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost48202 : endpointCostOK (48202, 49171, 33596) := by
  have h6147 := base_6147
  have h12293 : oddPrimeCount 12293 ≤ 1824 :=
    liftCount (m := 6147) (e := 12) (a := 800) (by decide) (by decide) (by decide) (by decide) (by decide) h6147
  have h24586 : oddPrimeCount 24586 ≤ 3715 :=
    liftCount (m := 12293) (e := 13) (a := 1824) (by decide) (by decide) (by decide) (by decide) (by decide) h12293
  have h49172 : oddPrimeCount 49172 ≤ 7227 :=
    liftCount (m := 24586) (e := 14) (a := 3715) (by decide) (by decide) (by decide) (by decide) (by decide) h24586
  have h98343 : oddPrimeCount 98343 ≤ 13783 :=
    liftCount (m := 49172) (e := 15) (a := 7227) (by decide) (by decide) (by decide) (by decide) (by decide) h49172
  exact endpointCost_of_parts (j := 49171) (a := 13783) (d := 19813)
    (by decide) h98343 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost49172 : endpointCostOK (49172, 50166, 34275) := by
  have h6271 := base_6271
  have h12542 : oddPrimeCount 12542 ≤ 1860 :=
    liftCount (m := 6271) (e := 12) (a := 815) (by decide) (by decide) (by decide) (by decide) (by decide) h6271
  have h25084 : oddPrimeCount 25084 ≤ 3789 :=
    liftCount (m := 12542) (e := 13) (a := 1860) (by decide) (by decide) (by decide) (by decide) (by decide) h12542
  have h50167 : oddPrimeCount 50167 ≤ 7372 :=
    liftCount (m := 25084) (e := 14) (a := 3789) (by decide) (by decide) (by decide) (by decide) (by decide) h25084
  have h100333 : oddPrimeCount 100333 ≤ 14060 :=
    liftCount (m := 50167) (e := 15) (a := 7372) (by decide) (by decide) (by decide) (by decide) (by decide) h50167
  exact endpointCost_of_parts (j := 50166) (a := 14060) (d := 20215)
    (by decide) h100333 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost50167 : endpointCostOK (50167, 51178, 34967) := by
  have h6398 := base_6398
  have h12795 : oddPrimeCount 12795 ≤ 1899 :=
    liftCount (m := 6398) (e := 12) (a := 833) (by decide) (by decide) (by decide) (by decide) (by decide) h6398
  have h25590 : oddPrimeCount 25590 ≤ 3867 :=
    liftCount (m := 12795) (e := 13) (a := 1899) (by decide) (by decide) (by decide) (by decide) (by decide) h12795
  have h51179 : oddPrimeCount 51179 ≤ 7522 :=
    liftCount (m := 25590) (e := 14) (a := 3867) (by decide) (by decide) (by decide) (by decide) (by decide) h25590
  have h102357 : oddPrimeCount 102357 ≤ 14345 :=
    liftCount (m := 51179) (e := 15) (a := 7522) (by decide) (by decide) (by decide) (by decide) (by decide) h51179
  exact endpointCost_of_parts (j := 51178) (a := 14345) (d := 20622)
    (by decide) h102357 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost51179 : endpointCostOK (51179, 52215, 35675) := by
  have h6527 := base_6527
  have h13054 : oddPrimeCount 13054 ≤ 1929 :=
    liftCount (m := 6527) (e := 12) (a := 842) (by decide) (by decide) (by decide) (by decide) (by decide) h6527
  have h26108 : oddPrimeCount 26108 ≤ 3937 :=
    liftCount (m := 13054) (e := 13) (a := 1929) (by decide) (by decide) (by decide) (by decide) (by decide) h13054
  have h52216 : oddPrimeCount 52216 ≤ 7666 :=
    liftCount (m := 26108) (e := 14) (a := 3937) (by decide) (by decide) (by decide) (by decide) (by decide) h26108
  have h104431 : oddPrimeCount 104431 ≤ 14628 :=
    liftCount (m := 52216) (e := 15) (a := 7666) (by decide) (by decide) (by decide) (by decide) (by decide) h52216
  exact endpointCost_of_parts (j := 52215) (a := 14628) (d := 21047)
    (by decide) h104431 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost52216 : endpointCostOK (52216, 53281, 36398) := by
  have h6661 := base_6661
  have h13321 : oddPrimeCount 13321 ≤ 1968 :=
    liftCount (m := 6661) (e := 12) (a := 858) (by decide) (by decide) (by decide) (by decide) (by decide) h6661
  have h26641 : oddPrimeCount 26641 ≤ 4017 :=
    liftCount (m := 13321) (e := 13) (a := 1968) (by decide) (by decide) (by decide) (by decide) (by decide) h13321
  have h53282 : oddPrimeCount 53282 ≤ 7822 :=
    liftCount (m := 26641) (e := 14) (a := 4017) (by decide) (by decide) (by decide) (by decide) (by decide) h26641
  have h106563 : oddPrimeCount 106563 ≤ 14926 :=
    liftCount (m := 53282) (e := 15) (a := 7822) (by decide) (by decide) (by decide) (by decide) (by decide) h53282
  exact endpointCost_of_parts (j := 53281) (a := 14926) (d := 21472)
    (by decide) h106563 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost53282 : endpointCostOK (53282, 54373, 37142) := by
  have h6797 := base_6797
  have h13594 : oddPrimeCount 13594 ≤ 2006 :=
    liftCount (m := 6797) (e := 12) (a := 874) (by decide) (by decide) (by decide) (by decide) (by decide) h6797
  have h27187 : oddPrimeCount 27187 ≤ 4097 :=
    liftCount (m := 13594) (e := 13) (a := 2006) (by decide) (by decide) (by decide) (by decide) (by decide) h13594
  have h54374 : oddPrimeCount 54374 ≤ 7980 :=
    liftCount (m := 27187) (e := 14) (a := 4097) (by decide) (by decide) (by decide) (by decide) (by decide) h27187
  have h108747 : oddPrimeCount 108747 ≤ 15229 :=
    liftCount (m := 54374) (e := 15) (a := 7980) (by decide) (by decide) (by decide) (by decide) (by decide) h54374
  exact endpointCost_of_parts (j := 54373) (a := 15229) (d := 21913)
    (by decide) h108747 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost54374 : endpointCostOK (54374, 55493, 37906) := by
  have h6937 := base_6937
  have h13874 : oddPrimeCount 13874 ≤ 2045 :=
    liftCount (m := 6937) (e := 12) (a := 889) (by decide) (by decide) (by decide) (by decide) (by decide) h6937
  have h27747 : oddPrimeCount 27747 ≤ 4179 :=
    liftCount (m := 13874) (e := 13) (a := 2045) (by decide) (by decide) (by decide) (by decide) (by decide) h13874
  have h55494 : oddPrimeCount 55494 ≤ 8142 :=
    liftCount (m := 27747) (e := 14) (a := 4179) (by decide) (by decide) (by decide) (by decide) (by decide) h27747
  have h110987 : oddPrimeCount 110987 ≤ 15541 :=
    liftCount (m := 55494) (e := 15) (a := 8142) (by decide) (by decide) (by decide) (by decide) (by decide) h55494
  exact endpointCost_of_parts (j := 55493) (a := 15541) (d := 22365)
    (by decide) h110987 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost55494 : endpointCostOK (55494, 56627, 38685) := by
  have h7079 := base_7079
  have h14157 : oddPrimeCount 14157 ≤ 2087 :=
    liftCount (m := 7079) (e := 12) (a := 908) (by decide) (by decide) (by decide) (by decide) (by decide) h7079
  have h28314 : oddPrimeCount 28314 ≤ 4265 :=
    liftCount (m := 14157) (e := 13) (a := 2087) (by decide) (by decide) (by decide) (by decide) (by decide) h14157
  have h56628 : oddPrimeCount 56628 ≤ 8309 :=
    liftCount (m := 28314) (e := 14) (a := 4265) (by decide) (by decide) (by decide) (by decide) (by decide) h28314
  have h113255 : oddPrimeCount 113255 ≤ 15859 :=
    liftCount (m := 56628) (e := 15) (a := 8309) (by decide) (by decide) (by decide) (by decide) (by decide) h56628
  exact endpointCost_of_parts (j := 56627) (a := 15859) (d := 22826)
    (by decide) h113255 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost56628 : endpointCostOK (56628, 57793, 39477) := by
  have h7225 := base_7225
  have h14449 : oddPrimeCount 14449 ≤ 2126 :=
    liftCount (m := 7225) (e := 12) (a := 922) (by decide) (by decide) (by decide) (by decide) (by decide) h7225
  have h28897 : oddPrimeCount 28897 ≤ 4348 :=
    liftCount (m := 14449) (e := 13) (a := 2126) (by decide) (by decide) (by decide) (by decide) (by decide) h14449
  have h57794 : oddPrimeCount 57794 ≤ 8476 :=
    liftCount (m := 28897) (e := 14) (a := 4348) (by decide) (by decide) (by decide) (by decide) (by decide) h28897
  have h115587 : oddPrimeCount 115587 ≤ 16181 :=
    liftCount (m := 57794) (e := 15) (a := 8476) (by decide) (by decide) (by decide) (by decide) (by decide) h57794
  exact endpointCost_of_parts (j := 57793) (a := 16181) (d := 23296)
    (by decide) h115587 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost57794 : endpointCostOK (57794, 58986, 40290) := by
  have h7374 := base_7374
  have h14747 : oddPrimeCount 14747 ≤ 2166 :=
    liftCount (m := 7374) (e := 12) (a := 937) (by decide) (by decide) (by decide) (by decide) (by decide) h7374
  have h29494 : oddPrimeCount 29494 ≤ 4434 :=
    liftCount (m := 14747) (e := 13) (a := 2166) (by decide) (by decide) (by decide) (by decide) (by decide) h14747
  have h58987 : oddPrimeCount 58987 ≤ 8647 :=
    liftCount (m := 29494) (e := 14) (a := 4434) (by decide) (by decide) (by decide) (by decide) (by decide) h29494
  have h117973 : oddPrimeCount 117973 ≤ 16511 :=
    liftCount (m := 58987) (e := 15) (a := 8647) (by decide) (by decide) (by decide) (by decide) (by decide) h58987
  exact endpointCost_of_parts (j := 58986) (a := 16511) (d := 23779)
    (by decide) h117973 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost58987 : endpointCostOK (58987, 60211, 41123) := by
  have h7527 := base_7527
  have h15053 : oddPrimeCount 15053 ≤ 2206 :=
    liftCount (m := 7527) (e := 12) (a := 952) (by decide) (by decide) (by decide) (by decide) (by decide) h7527
  have h30106 : oddPrimeCount 30106 ≤ 4521 :=
    liftCount (m := 15053) (e := 13) (a := 2206) (by decide) (by decide) (by decide) (by decide) (by decide) h15053
  have h60212 : oddPrimeCount 60212 ≤ 8821 :=
    liftCount (m := 30106) (e := 14) (a := 4521) (by decide) (by decide) (by decide) (by decide) (by decide) h30106
  have h120423 : oddPrimeCount 120423 ≤ 16849 :=
    liftCount (m := 60212) (e := 15) (a := 8821) (by decide) (by decide) (by decide) (by decide) (by decide) h60212
  exact endpointCost_of_parts (j := 60211) (a := 16849) (d := 24274)
    (by decide) h120423 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost60212 : endpointCostOK (60212, 61457, 41977) := by
  have h7683 := base_7683
  have h15365 : oddPrimeCount 15365 ≤ 2253 :=
    liftCount (m := 7683) (e := 12) (a := 973) (by decide) (by decide) (by decide) (by decide) (by decide) h7683
  have h30729 : oddPrimeCount 30729 ≤ 4616 :=
    liftCount (m := 15365) (e := 13) (a := 2253) (by decide) (by decide) (by decide) (by decide) (by decide) h15365
  have h61458 : oddPrimeCount 61458 ≤ 9005 :=
    liftCount (m := 30729) (e := 14) (a := 4616) (by decide) (by decide) (by decide) (by decide) (by decide) h30729
  have h122915 : oddPrimeCount 122915 ≤ 17199 :=
    liftCount (m := 61458) (e := 15) (a := 9005) (by decide) (by decide) (by decide) (by decide) (by decide) h61458
  exact endpointCost_of_parts (j := 61457) (a := 17199) (d := 24778)
    (by decide) h122915 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost61458 : endpointCostOK (61458, 62743, 42849) := by
  have h7843 := base_7843
  have h15686 : oddPrimeCount 15686 ≤ 2297 :=
    liftCount (m := 7843) (e := 12) (a := 990) (by decide) (by decide) (by decide) (by decide) (by decide) h7843
  have h31372 : oddPrimeCount 31372 ≤ 4710 :=
    liftCount (m := 15686) (e := 13) (a := 2297) (by decide) (by decide) (by decide) (by decide) (by decide) h15686
  have h62744 : oddPrimeCount 62744 ≤ 9191 :=
    liftCount (m := 31372) (e := 14) (a := 4710) (by decide) (by decide) (by decide) (by decide) (by decide) h31372
  have h125487 : oddPrimeCount 125487 ≤ 17556 :=
    liftCount (m := 62744) (e := 15) (a := 9191) (by decide) (by decide) (by decide) (by decide) (by decide) h62744
  exact endpointCost_of_parts (j := 62743) (a := 17556) (d := 25293)
    (by decide) h125487 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost62744 : endpointCostOK (62744, 64060, 43746) := by
  have h8008 := base_8008
  have h16016 : oddPrimeCount 16016 ≤ 2340 :=
    liftCount (m := 8008) (e := 12) (a := 1006) (by decide) (by decide) (by decide) (by decide) (by decide) h8008
  have h32031 : oddPrimeCount 32031 ≤ 4804 :=
    liftCount (m := 16016) (e := 13) (a := 2340) (by decide) (by decide) (by decide) (by decide) (by decide) h16016
  have h64061 : oddPrimeCount 64061 ≤ 9379 :=
    liftCount (m := 32031) (e := 14) (a := 4804) (by decide) (by decide) (by decide) (by decide) (by decide) h32031
  have h128121 : oddPrimeCount 128121 ≤ 17920 :=
    liftCount (m := 64061) (e := 15) (a := 9379) (by decide) (by decide) (by decide) (by decide) (by decide) h64061
  exact endpointCost_of_parts (j := 64060) (a := 17920) (d := 25826)
    (by decide) h128121 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost64061 : endpointCostOK (64061, 67621, 44996) := by
  have h8453 := base_8453
  have h16906 : oddPrimeCount 16906 ≤ 2356 :=
    liftCount (m := 8453) (e := 13) (a := 1056) (by decide) (by decide) (by decide) (by decide) (by decide) h8453
  have h33811 : oddPrimeCount 33811 ≤ 4771 :=
    liftCount (m := 16906) (e := 14) (a := 2356) (by decide) (by decide) (by decide) (by decide) (by decide) h16906
  have h67622 : oddPrimeCount 67622 ≤ 9279 :=
    liftCount (m := 33811) (e := 15) (a := 4771) (by decide) (by decide) (by decide) (by decide) (by decide) h33811
  have h135243 : oddPrimeCount 135243 ≤ 17731 :=
    liftCount (m := 67622) (e := 16) (a := 9279) (by decide) (by decide) (by decide) (by decide) (by decide) h67622
  exact endpointCost_of_parts (j := 67621) (a := 17731) (d := 27265)
    (by decide) h135243 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost67622 : endpointCostOK (67622, 71392, 47499) := by
  have h8925 := base_8925
  have h17849 : oddPrimeCount 17849 ≤ 2481 :=
    liftCount (m := 8925) (e := 13) (a := 1108) (by decide) (by decide) (by decide) (by decide) (by decide) h8925
  have h35697 : oddPrimeCount 35697 ≤ 5030 :=
    liftCount (m := 17849) (e := 14) (a := 2481) (by decide) (by decide) (by decide) (by decide) (by decide) h17849
  have h71393 : oddPrimeCount 71393 ≤ 9789 :=
    liftCount (m := 35697) (e := 15) (a := 5030) (by decide) (by decide) (by decide) (by decide) (by decide) h35697
  have h142785 : oddPrimeCount 142785 ≤ 18713 :=
    liftCount (m := 71393) (e := 16) (a := 9789) (by decide) (by decide) (by decide) (by decide) (by decide) h71393
  exact endpointCost_of_parts (j := 71392) (a := 18713) (d := 28786)
    (by decide) h142785 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost71393 : endpointCostOK (71393, 75374, 50149) := by
  have h9422 := base_9422
  have h18844 : oddPrimeCount 18844 ≤ 2614 :=
    liftCount (m := 9422) (e := 13) (a := 1165) (by decide) (by decide) (by decide) (by decide) (by decide) h9422
  have h37688 : oddPrimeCount 37688 ≤ 5306 :=
    liftCount (m := 18844) (e := 14) (a := 2614) (by decide) (by decide) (by decide) (by decide) (by decide) h18844
  have h75375 : oddPrimeCount 75375 ≤ 10331 :=
    liftCount (m := 37688) (e := 15) (a := 5306) (by decide) (by decide) (by decide) (by decide) (by decide) h37688
  have h150749 : oddPrimeCount 150749 ≤ 19752 :=
    liftCount (m := 75375) (e := 16) (a := 10331) (by decide) (by decide) (by decide) (by decide) (by decide) h75375
  exact endpointCost_of_parts (j := 75374) (a := 19752) (d := 30397)
    (by decide) h150749 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost75375 : endpointCostOK (75375, 79582, 52947) := by
  have h9948 := base_9948
  have h19896 : oddPrimeCount 19896 ≤ 2755 :=
    liftCount (m := 9948) (e := 13) (a := 1225) (by decide) (by decide) (by decide) (by decide) (by decide) h9948
  have h39792 : oddPrimeCount 39792 ≤ 5597 :=
    liftCount (m := 19896) (e := 14) (a := 2755) (by decide) (by decide) (by decide) (by decide) (by decide) h19896
  have h79583 : oddPrimeCount 79583 ≤ 10902 :=
    liftCount (m := 39792) (e := 15) (a := 5597) (by decide) (by decide) (by decide) (by decide) (by decide) h39792
  have h159165 : oddPrimeCount 159165 ≤ 20849 :=
    liftCount (m := 79583) (e := 16) (a := 10902) (by decide) (by decide) (by decide) (by decide) (by decide) h79583
  exact endpointCost_of_parts (j := 79582) (a := 20849) (d := 32098)
    (by decide) h159165 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost79583 : endpointCostOK (79583, 83487, 55823) := by
  have h5218 := base_5218
  have h10436 : oddPrimeCount 10436 ≤ 1561 :=
    liftCount (m := 5218) (e := 12) (a := 692) (by decide) (by decide) (by decide) (by decide) (by decide) h5218
  have h20872 : oddPrimeCount 20872 ≤ 3166 :=
    liftCount (m := 10436) (e := 13) (a := 1561) (by decide) (by decide) (by decide) (by decide) (by decide) h10436
  have h41744 : oddPrimeCount 41744 ≤ 6147 :=
    liftCount (m := 20872) (e := 14) (a := 3166) (by decide) (by decide) (by decide) (by decide) (by decide) h20872
  have h83488 : oddPrimeCount 83488 ≤ 11712 :=
    liftCount (m := 41744) (e := 15) (a := 6147) (by decide) (by decide) (by decide) (by decide) (by decide) h41744
  have h166975 : oddPrimeCount 166975 ≤ 22148 :=
    liftCount (m := 83488) (e := 16) (a := 11712) (by decide) (by decide) (by decide) (by decide) (by decide) h83488
  exact endpointCost_of_parts (j := 83487) (a := 22148) (d := 33675)
    (by decide) h166975 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost83488 : endpointCostOK (83488, 87583, 58563) := by
  have h5474 := base_5474
  have h10948 : oddPrimeCount 10948 ≤ 1633 :=
    liftCount (m := 5474) (e := 12) (a := 721) (by decide) (by decide) (by decide) (by decide) (by decide) h5474
  have h21896 : oddPrimeCount 21896 ≤ 3317 :=
    liftCount (m := 10948) (e := 13) (a := 1633) (by decide) (by decide) (by decide) (by decide) (by decide) h10948
  have h43792 : oddPrimeCount 43792 ≤ 6445 :=
    liftCount (m := 21896) (e := 14) (a := 3317) (by decide) (by decide) (by decide) (by decide) (by decide) h21896
  have h87584 : oddPrimeCount 87584 ≤ 12283 :=
    liftCount (m := 43792) (e := 15) (a := 6445) (by decide) (by decide) (by decide) (by decide) (by decide) h43792
  have h175167 : oddPrimeCount 175167 ≤ 23231 :=
    liftCount (m := 87584) (e := 16) (a := 12283) (by decide) (by decide) (by decide) (by decide) (by decide) h87584
  exact endpointCost_of_parts (j := 87583) (a := 23231) (d := 35332)
    (by decide) h175167 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost87584 : endpointCostOK (87584, 91885, 61438) := by
  have h5743 := base_5743
  have h11486 : oddPrimeCount 11486 ≤ 1712 :=
    liftCount (m := 5743) (e := 12) (a := 755) (by decide) (by decide) (by decide) (by decide) (by decide) h5743
  have h22972 : oddPrimeCount 22972 ≤ 3479 :=
    liftCount (m := 11486) (e := 13) (a := 1712) (by decide) (by decide) (by decide) (by decide) (by decide) h11486
  have h45943 : oddPrimeCount 45943 ≤ 6760 :=
    liftCount (m := 22972) (e := 14) (a := 3479) (by decide) (by decide) (by decide) (by decide) (by decide) h22972
  have h91886 : oddPrimeCount 91886 ≤ 12885 :=
    liftCount (m := 45943) (e := 15) (a := 6760) (by decide) (by decide) (by decide) (by decide) (by decide) h45943
  have h183771 : oddPrimeCount 183771 ≤ 24370 :=
    liftCount (m := 91886) (e := 16) (a := 12885) (by decide) (by decide) (by decide) (by decide) (by decide) h91886
  exact endpointCost_of_parts (j := 91885) (a := 24370) (d := 37068)
    (by decide) h183771 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost91886 : endpointCostOK (91886, 96414, 64459) := by
  have h6026 := base_6026
  have h12052 : oddPrimeCount 12052 ≤ 1788 :=
    liftCount (m := 6026) (e := 12) (a := 784) (by decide) (by decide) (by decide) (by decide) (by decide) h6026
  have h24104 : oddPrimeCount 24104 ≤ 3642 :=
    liftCount (m := 12052) (e := 13) (a := 1788) (by decide) (by decide) (by decide) (by decide) (by decide) h12052
  have h48208 : oddPrimeCount 48208 ≤ 7085 :=
    liftCount (m := 24104) (e := 14) (a := 3642) (by decide) (by decide) (by decide) (by decide) (by decide) h24104
  have h96415 : oddPrimeCount 96415 ≤ 13512 :=
    liftCount (m := 48208) (e := 15) (a := 7085) (by decide) (by decide) (by decide) (by decide) (by decide) h48208
  have h192829 : oddPrimeCount 192829 ≤ 25563 :=
    liftCount (m := 96415) (e := 16) (a := 13512) (by decide) (by decide) (by decide) (by decide) (by decide) h96415
  exact endpointCost_of_parts (j := 96414) (a := 25563) (d := 38896)
    (by decide) h192829 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost96415 : endpointCostOK (96415, 101151, 67635) := by
  have h6322 := base_6322
  have h12644 : oddPrimeCount 12644 ≤ 1874 :=
    liftCount (m := 6322) (e := 12) (a := 821) (by decide) (by decide) (by decide) (by decide) (by decide) h6322
  have h25288 : oddPrimeCount 25288 ≤ 3819 :=
    liftCount (m := 12644) (e := 13) (a := 1874) (by decide) (by decide) (by decide) (by decide) (by decide) h12644
  have h50576 : oddPrimeCount 50576 ≤ 7431 :=
    liftCount (m := 25288) (e := 14) (a := 3819) (by decide) (by decide) (by decide) (by decide) (by decide) h25288
  have h101152 : oddPrimeCount 101152 ≤ 14174 :=
    liftCount (m := 50576) (e := 15) (a := 7431) (by decide) (by decide) (by decide) (by decide) (by decide) h50576
  have h202303 : oddPrimeCount 202303 ≤ 26818 :=
    liftCount (m := 101152) (e := 16) (a := 14174) (by decide) (by decide) (by decide) (by decide) (by decide) h101152
  exact endpointCost_of_parts (j := 101151) (a := 26818) (d := 40817)
    (by decide) h202303 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost101152 : endpointCostOK (101152, 106141, 70962) := by
  have h6634 := base_6634
  have h13268 : oddPrimeCount 13268 ≤ 1959 :=
    liftCount (m := 6634) (e := 12) (a := 854) (by decide) (by decide) (by decide) (by decide) (by decide) h6634
  have h26536 : oddPrimeCount 26536 ≤ 4000 :=
    liftCount (m := 13268) (e := 13) (a := 1959) (by decide) (by decide) (by decide) (by decide) (by decide) h13268
  have h53071 : oddPrimeCount 53071 ≤ 7790 :=
    liftCount (m := 26536) (e := 14) (a := 4000) (by decide) (by decide) (by decide) (by decide) (by decide) h26536
  have h106142 : oddPrimeCount 106142 ≤ 14866 :=
    liftCount (m := 53071) (e := 15) (a := 7790) (by decide) (by decide) (by decide) (by decide) (by decide) h53071
  have h212283 : oddPrimeCount 212283 ≤ 28133 :=
    liftCount (m := 106142) (e := 16) (a := 14866) (by decide) (by decide) (by decide) (by decide) (by decide) h106142
  exact endpointCost_of_parts (j := 106141) (a := 28133) (d := 42829)
    (by decide) h212283 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost106142 : endpointCostOK (106142, 111382, 74465) := by
  have h6962 := base_6962
  have h13923 : oddPrimeCount 13923 ≤ 2053 :=
    liftCount (m := 6962) (e := 12) (a := 893) (by decide) (by decide) (by decide) (by decide) (by decide) h6962
  have h27846 : oddPrimeCount 27846 ≤ 4195 :=
    liftCount (m := 13923) (e := 13) (a := 2053) (by decide) (by decide) (by decide) (by decide) (by decide) h13923
  have h55692 : oddPrimeCount 55692 ≤ 8173 :=
    liftCount (m := 27846) (e := 14) (a := 4195) (by decide) (by decide) (by decide) (by decide) (by decide) h27846
  have h111383 : oddPrimeCount 111383 ≤ 15598 :=
    liftCount (m := 55692) (e := 15) (a := 8173) (by decide) (by decide) (by decide) (by decide) (by decide) h55692
  have h222765 : oddPrimeCount 222765 ≤ 29520 :=
    liftCount (m := 111383) (e := 16) (a := 15598) (by decide) (by decide) (by decide) (by decide) (by decide) h111383
  exact endpointCost_of_parts (j := 111382) (a := 29520) (d := 44945)
    (by decide) h222765 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost111383 : endpointCostOK (111383, 116887, 78141) := by
  have h7306 := base_7306
  have h14611 : oddPrimeCount 14611 ≤ 2146 :=
    liftCount (m := 7306) (e := 12) (a := 929) (by decide) (by decide) (by decide) (by decide) (by decide) h7306
  have h29222 : oddPrimeCount 29222 ≤ 4393 :=
    liftCount (m := 14611) (e := 13) (a := 2146) (by decide) (by decide) (by decide) (by decide) (by decide) h14611
  have h58444 : oddPrimeCount 58444 ≤ 8567 :=
    liftCount (m := 29222) (e := 14) (a := 4393) (by decide) (by decide) (by decide) (by decide) (by decide) h29222
  have h116888 : oddPrimeCount 116888 ≤ 16359 :=
    liftCount (m := 58444) (e := 15) (a := 8567) (by decide) (by decide) (by decide) (by decide) (by decide) h58444
  have h233775 : oddPrimeCount 233775 ≤ 30970 :=
    liftCount (m := 116888) (e := 16) (a := 16359) (by decide) (by decide) (by decide) (by decide) (by decide) h116888
  exact endpointCost_of_parts (j := 116887) (a := 30970) (d := 47171)
    (by decide) h233775 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost116888 : endpointCostOK (116888, 122667, 82005) := by
  have h7667 := base_7667
  have h15334 : oddPrimeCount 15334 ≤ 2247 :=
    liftCount (m := 7667) (e := 12) (a := 970) (by decide) (by decide) (by decide) (by decide) (by decide) h7667
  have h30667 : oddPrimeCount 30667 ≤ 4606 :=
    liftCount (m := 15334) (e := 13) (a := 2247) (by decide) (by decide) (by decide) (by decide) (by decide) h15334
  have h61334 : oddPrimeCount 61334 ≤ 8987 :=
    liftCount (m := 30667) (e := 14) (a := 4606) (by decide) (by decide) (by decide) (by decide) (by decide) h30667
  have h122668 : oddPrimeCount 122668 ≤ 17164 :=
    liftCount (m := 61334) (e := 15) (a := 8987) (by decide) (by decide) (by decide) (by decide) (by decide) h61334
  have h245335 : oddPrimeCount 245335 ≤ 32497 :=
    liftCount (m := 122668) (e := 16) (a := 17164) (by decide) (by decide) (by decide) (by decide) (by decide) h122668
  exact endpointCost_of_parts (j := 122667) (a := 32497) (d := 49508)
    (by decide) h245335 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost122668 : endpointCostOK (122668, 128743, 86061) := by
  have h8047 := base_8047
  have h16093 : oddPrimeCount 16093 ≤ 2351 :=
    liftCount (m := 8047) (e := 12) (a := 1010) (by decide) (by decide) (by decide) (by decide) (by decide) h8047
  have h32186 : oddPrimeCount 32186 ≤ 4826 :=
    liftCount (m := 16093) (e := 13) (a := 2351) (by decide) (by decide) (by decide) (by decide) (by decide) h16093
  have h64372 : oddPrimeCount 64372 ≤ 9424 :=
    liftCount (m := 32186) (e := 14) (a := 4826) (by decide) (by decide) (by decide) (by decide) (by decide) h32186
  have h128744 : oddPrimeCount 128744 ≤ 18006 :=
    liftCount (m := 64372) (e := 15) (a := 9424) (by decide) (by decide) (by decide) (by decide) (by decide) h64372
  have h257487 : oddPrimeCount 257487 ≤ 34099 :=
    liftCount (m := 128744) (e := 16) (a := 18006) (by decide) (by decide) (by decide) (by decide) (by decide) h128744
  exact endpointCost_of_parts (j := 128743) (a := 34099) (d := 51962)
    (by decide) h257487 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost128744 : endpointCostOK (128744, 139444, 90971) := by
  have h8716 := base_8716
  have h17431 : oddPrimeCount 17431 ≤ 2425 :=
    liftCount (m := 8716) (e := 13) (a := 1085) (by decide) (by decide) (by decide) (by decide) (by decide) h8716
  have h34862 : oddPrimeCount 34862 ≤ 4915 :=
    liftCount (m := 17431) (e := 14) (a := 2425) (by decide) (by decide) (by decide) (by decide) (by decide) h17431
  have h69723 : oddPrimeCount 69723 ≤ 9563 :=
    liftCount (m := 34862) (e := 15) (a := 4915) (by decide) (by decide) (by decide) (by decide) (by decide) h34862
  have h139445 : oddPrimeCount 139445 ≤ 18278 :=
    liftCount (m := 69723) (e := 16) (a := 9563) (by decide) (by decide) (by decide) (by decide) (by decide) h69723
  have h278889 : oddPrimeCount 278889 ≤ 34683 :=
    liftCount (m := 139445) (e := 17) (a := 18278) (by decide) (by decide) (by decide) (by decide) (by decide) h139445
  exact endpointCost_of_parts (j := 139444) (a := 34683) (d := 56288)
    (by decide) h278889 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost139445 : endpointCostOK (139445, 151037, 98532) := by
  have h9440 := base_9440
  have h18880 : oddPrimeCount 18880 ≤ 2621 :=
    liftCount (m := 9440) (e := 13) (a := 1169) (by decide) (by decide) (by decide) (by decide) (by decide) h9440
  have h37760 : oddPrimeCount 37760 ≤ 5318 :=
    liftCount (m := 18880) (e := 14) (a := 2621) (by decide) (by decide) (by decide) (by decide) (by decide) h18880
  have h75519 : oddPrimeCount 75519 ≤ 10352 :=
    liftCount (m := 37760) (e := 15) (a := 5318) (by decide) (by decide) (by decide) (by decide) (by decide) h37760
  have h151038 : oddPrimeCount 151038 ≤ 19791 :=
    liftCount (m := 75519) (e := 16) (a := 10352) (by decide) (by decide) (by decide) (by decide) (by decide) h75519
  have h302075 : oddPrimeCount 302075 ≤ 37560 :=
    liftCount (m := 151038) (e := 17) (a := 19791) (by decide) (by decide) (by decide) (by decide) (by decide) h151038
  exact endpointCost_of_parts (j := 151037) (a := 37560) (d := 60972)
    (by decide) h302075 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost151038 : endpointCostOK (151038, 163057, 106647) := by
  have h5096 := base_5096
  have h10192 : oddPrimeCount 10192 ≤ 1528 :=
    liftCount (m := 5096) (e := 12) (a := 679) (by decide) (by decide) (by decide) (by decide) (by decide) h5096
  have h20383 : oddPrimeCount 20383 ≤ 3096 :=
    liftCount (m := 10192) (e := 13) (a := 1528) (by decide) (by decide) (by decide) (by decide) (by decide) h10192
  have h40765 : oddPrimeCount 40765 ≤ 6007 :=
    liftCount (m := 20383) (e := 14) (a := 3096) (by decide) (by decide) (by decide) (by decide) (by decide) h20383
  have h81529 : oddPrimeCount 81529 ≤ 11442 :=
    liftCount (m := 40765) (e := 15) (a := 6007) (by decide) (by decide) (by decide) (by decide) (by decide) h40765
  have h163058 : oddPrimeCount 163058 ≤ 21633 :=
    liftCount (m := 81529) (e := 16) (a := 11442) (by decide) (by decide) (by decide) (by decide) (by decide) h81529
  have h326115 : oddPrimeCount 326115 ≤ 40816 :=
    liftCount (m := 163058) (e := 17) (a := 21633) (by decide) (by decide) (by decide) (by decide) (by decide) h163058
  exact endpointCost_of_parts (j := 163057) (a := 40816) (d := 65831)
    (by decide) h326115 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost163058 : endpointCostOK (163058, 176048, 115137) := by
  have h5502 := base_5502
  have h11004 : oddPrimeCount 11004 ≤ 1642 :=
    liftCount (m := 5502) (e := 12) (a := 725) (by decide) (by decide) (by decide) (by decide) (by decide) h5502
  have h22007 : oddPrimeCount 22007 ≤ 3334 :=
    liftCount (m := 11004) (e := 13) (a := 1642) (by decide) (by decide) (by decide) (by decide) (by decide) h11004
  have h44013 : oddPrimeCount 44013 ≤ 6477 :=
    liftCount (m := 22007) (e := 14) (a := 3334) (by decide) (by decide) (by decide) (by decide) (by decide) h22007
  have h88025 : oddPrimeCount 88025 ≤ 12345 :=
    liftCount (m := 44013) (e := 15) (a := 6477) (by decide) (by decide) (by decide) (by decide) (by decide) h44013
  have h176049 : oddPrimeCount 176049 ≤ 23348 :=
    liftCount (m := 88025) (e := 16) (a := 12345) (by decide) (by decide) (by decide) (by decide) (by decide) h88025
  have h352097 : oddPrimeCount 352097 ≤ 44059 :=
    liftCount (m := 176049) (e := 17) (a := 23348) (by decide) (by decide) (by decide) (by decide) (by decide) h176049
  exact endpointCost_of_parts (j := 176048) (a := 44059) (d := 71078)
    (by decide) h352097 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost176049 : endpointCostOK (176049, 190066, 124310) := by
  have h5940 := base_5940
  have h11880 : oddPrimeCount 11880 ≤ 1769 :=
    liftCount (m := 5940) (e := 12) (a := 779) (by decide) (by decide) (by decide) (by decide) (by decide) h5940
  have h23759 : oddPrimeCount 23759 ≤ 3596 :=
    liftCount (m := 11880) (e := 13) (a := 1769) (by decide) (by decide) (by decide) (by decide) (by decide) h11880
  have h47517 : oddPrimeCount 47517 ≤ 6990 :=
    liftCount (m := 23759) (e := 14) (a := 3596) (by decide) (by decide) (by decide) (by decide) (by decide) h23759
  have h95034 : oddPrimeCount 95034 ≤ 13325 :=
    liftCount (m := 47517) (e := 15) (a := 6990) (by decide) (by decide) (by decide) (by decide) (by decide) h47517
  have h190067 : oddPrimeCount 190067 ≤ 25204 :=
    liftCount (m := 95034) (e := 16) (a := 13325) (by decide) (by decide) (by decide) (by decide) (by decide) h95034
  have h380133 : oddPrimeCount 380133 ≤ 47564 :=
    liftCount (m := 190067) (e := 17) (a := 25204) (by decide) (by decide) (by decide) (by decide) (by decide) h190067
  exact endpointCost_of_parts (j := 190066) (a := 47564) (d := 76746)
    (by decide) h380133 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost190067 : endpointCostOK (190067, 205208, 134210) := by
  have h6413 := base_6413
  have h12826 : oddPrimeCount 12826 ≤ 1901 :=
    liftCount (m := 6413) (e := 12) (a := 833) (by decide) (by decide) (by decide) (by decide) (by decide) h6413
  have h25652 : oddPrimeCount 25652 ≤ 3874 :=
    liftCount (m := 12826) (e := 13) (a := 1901) (by decide) (by decide) (by decide) (by decide) (by decide) h12826
  have h51303 : oddPrimeCount 51303 ≤ 7538 :=
    liftCount (m := 25652) (e := 14) (a := 3874) (by decide) (by decide) (by decide) (by decide) (by decide) h25652
  have h102605 : oddPrimeCount 102605 ≤ 14378 :=
    liftCount (m := 51303) (e := 15) (a := 7538) (by decide) (by decide) (by decide) (by decide) (by decide) h51303
  have h205209 : oddPrimeCount 205209 ≤ 27203 :=
    liftCount (m := 102605) (e := 16) (a := 14378) (by decide) (by decide) (by decide) (by decide) (by decide) h102605
  have h410417 : oddPrimeCount 410417 ≤ 51345 :=
    liftCount (m := 205209) (e := 17) (a := 27203) (by decide) (by decide) (by decide) (by decide) (by decide) h205209
  exact endpointCost_of_parts (j := 205208) (a := 51345) (d := 82865)
    (by decide) h410417 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost205209 : endpointCostOK (205209, 221566, 144907) := by
  have h6924 := base_6924
  have h13848 : oddPrimeCount 13848 ≤ 2043 :=
    liftCount (m := 6924) (e := 12) (a := 889) (by decide) (by decide) (by decide) (by decide) (by decide) h6924
  have h27696 : oddPrimeCount 27696 ≤ 4173 :=
    liftCount (m := 13848) (e := 13) (a := 2043) (by decide) (by decide) (by decide) (by decide) (by decide) h13848
  have h55392 : oddPrimeCount 55392 ≤ 8129 :=
    liftCount (m := 27696) (e := 14) (a := 4173) (by decide) (by decide) (by decide) (by decide) (by decide) h27696
  have h110784 : oddPrimeCount 110784 ≤ 15514 :=
    liftCount (m := 55392) (e := 15) (a := 8129) (by decide) (by decide) (by decide) (by decide) (by decide) h55392
  have h221567 : oddPrimeCount 221567 ≤ 29362 :=
    liftCount (m := 110784) (e := 16) (a := 15514) (by decide) (by decide) (by decide) (by decide) (by decide) h110784
  have h443133 : oddPrimeCount 443133 ≤ 55428 :=
    liftCount (m := 221567) (e := 17) (a := 29362) (by decide) (by decide) (by decide) (by decide) (by decide) h221567
  exact endpointCost_of_parts (j := 221566) (a := 55428) (d := 89479)
    (by decide) h443133 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost221567 : endpointCostOK (221567, 239251, 156462) := by
  have h7477 := base_7477
  have h14954 : oddPrimeCount 14954 ≤ 2191 :=
    liftCount (m := 7477) (e := 12) (a := 945) (by decide) (by decide) (by decide) (by decide) (by decide) h7477
  have h29907 : oddPrimeCount 29907 ≤ 4491 :=
    liftCount (m := 14954) (e := 13) (a := 2191) (by decide) (by decide) (by decide) (by decide) (by decide) h14954
  have h59813 : oddPrimeCount 59813 ≤ 8763 :=
    liftCount (m := 29907) (e := 14) (a := 4491) (by decide) (by decide) (by decide) (by decide) (by decide) h29907
  have h119626 : oddPrimeCount 119626 ≤ 16738 :=
    liftCount (m := 59813) (e := 15) (a := 8763) (by decide) (by decide) (by decide) (by decide) (by decide) h59813
  have h239252 : oddPrimeCount 239252 ≤ 31691 :=
    liftCount (m := 119626) (e := 16) (a := 16738) (by decide) (by decide) (by decide) (by decide) (by decide) h119626
  have h478503 : oddPrimeCount 478503 ≤ 59838 :=
    liftCount (m := 239252) (e := 17) (a := 31691) (by decide) (by decide) (by decide) (by decide) (by decide) h239252
  exact endpointCost_of_parts (j := 239251) (a := 59838) (d := 96624)
    (by decide) h478503 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost239252 : endpointCostOK (239252, 258340, 168951) := by
  have h8074 := base_8074
  have h16147 : oddPrimeCount 16147 ≤ 2358 :=
    liftCount (m := 8074) (e := 12) (a := 1013) (by decide) (by decide) (by decide) (by decide) (by decide) h8074
  have h32293 : oddPrimeCount 32293 ≤ 4842 :=
    liftCount (m := 16147) (e := 13) (a := 2358) (by decide) (by decide) (by decide) (by decide) (by decide) h16147
  have h64586 : oddPrimeCount 64586 ≤ 9455 :=
    liftCount (m := 32293) (e := 14) (a := 4842) (by decide) (by decide) (by decide) (by decide) (by decide) h32293
  have h129171 : oddPrimeCount 129171 ≤ 18066 :=
    liftCount (m := 64586) (e := 15) (a := 9455) (by decide) (by decide) (by decide) (by decide) (by decide) h64586
  have h258341 : oddPrimeCount 258341 ≤ 34212 :=
    liftCount (m := 129171) (e := 16) (a := 18066) (by decide) (by decide) (by decide) (by decide) (by decide) h129171
  have h516681 : oddPrimeCount 516681 ≤ 64605 :=
    liftCount (m := 258341) (e := 17) (a := 34212) (by decide) (by decide) (by decide) (by decide) (by decide) h258341
  exact endpointCost_of_parts (j := 258340) (a := 64605) (d := 104346)
    (by decide) h516681 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost258341 : endpointCostOK (258341, 287261, 183670) := by
  have h8977 := base_8977
  have h17954 : oddPrimeCount 17954 ≤ 2496 :=
    liftCount (m := 8977) (e := 13) (a := 1115) (by decide) (by decide) (by decide) (by decide) (by decide) h8977
  have h35908 : oddPrimeCount 35908 ≤ 5060 :=
    liftCount (m := 17954) (e := 14) (a := 2496) (by decide) (by decide) (by decide) (by decide) (by decide) h17954
  have h71816 : oddPrimeCount 71816 ≤ 9847 :=
    liftCount (m := 35908) (e := 15) (a := 5060) (by decide) (by decide) (by decide) (by decide) (by decide) h35908
  have h143631 : oddPrimeCount 143631 ≤ 18824 :=
    liftCount (m := 71816) (e := 16) (a := 9847) (by decide) (by decide) (by decide) (by decide) (by decide) h71816
  have h287262 : oddPrimeCount 287262 ≤ 35721 :=
    liftCount (m := 143631) (e := 17) (a := 18824) (by decide) (by decide) (by decide) (by decide) (by decide) h143631
  have h574523 : oddPrimeCount 574523 ≤ 67639 :=
    liftCount (m := 287262) (e := 18) (a := 35721) (by decide) (by decide) (by decide) (by decide) (by decide) h287262
  exact endpointCost_of_parts (j := 287261) (a := 67639) (d := 116031)
    (by decide) h574523 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost287262 : endpointCostOK (287262, 319423, 204234) := by
  have h9982 := base_9982
  have h19964 : oddPrimeCount 19964 ≤ 2763 :=
    liftCount (m := 9982) (e := 13) (a := 1228) (by decide) (by decide) (by decide) (by decide) (by decide) h9982
  have h39928 : oddPrimeCount 39928 ≤ 5615 :=
    liftCount (m := 19964) (e := 14) (a := 2763) (by decide) (by decide) (by decide) (by decide) (by decide) h19964
  have h79856 : oddPrimeCount 79856 ≤ 10938 :=
    liftCount (m := 39928) (e := 15) (a := 5615) (by decide) (by decide) (by decide) (by decide) (by decide) h39928
  have h159712 : oddPrimeCount 159712 ≤ 20920 :=
    liftCount (m := 79856) (e := 16) (a := 10938) (by decide) (by decide) (by decide) (by decide) (by decide) h79856
  have h319424 : oddPrimeCount 319424 ≤ 39709 :=
    liftCount (m := 159712) (e := 17) (a := 20920) (by decide) (by decide) (by decide) (by decide) (by decide) h159712
  have h638847 : oddPrimeCount 638847 ≤ 75200 :=
    liftCount (m := 319424) (e := 18) (a := 39709) (by decide) (by decide) (by decide) (by decide) (by decide) h319424
  exact endpointCost_of_parts (j := 319423) (a := 75200) (d := 129034)
    (by decide) h638847 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost319424 : endpointCostOK (319424, 354577, 227012) := by
  have h5541 := base_5541
  have h11081 : oddPrimeCount 11081 ≤ 1654 :=
    liftCount (m := 5541) (e := 12) (a := 731) (by decide) (by decide) (by decide) (by decide) (by decide) h5541
  have h22162 : oddPrimeCount 22162 ≤ 3358 :=
    liftCount (m := 11081) (e := 13) (a := 1654) (by decide) (by decide) (by decide) (by decide) (by decide) h11081
  have h44323 : oddPrimeCount 44323 ≤ 6524 :=
    liftCount (m := 22162) (e := 14) (a := 3358) (by decide) (by decide) (by decide) (by decide) (by decide) h22162
  have h88645 : oddPrimeCount 88645 ≤ 12433 :=
    liftCount (m := 44323) (e := 15) (a := 6524) (by decide) (by decide) (by decide) (by decide) (by decide) h44323
  have h177289 : oddPrimeCount 177289 ≤ 23513 :=
    liftCount (m := 88645) (e := 16) (a := 12433) (by decide) (by decide) (by decide) (by decide) (by decide) h88645
  have h354578 : oddPrimeCount 354578 ≤ 44370 :=
    liftCount (m := 177289) (e := 17) (a := 23513) (by decide) (by decide) (by decide) (by decide) (by decide) h177289
  have h709155 : oddPrimeCount 709155 ≤ 83767 :=
    liftCount (m := 354578) (e := 18) (a := 44370) (by decide) (by decide) (by decide) (by decide) (by decide) h354578
  exact endpointCost_of_parts (j := 354577) (a := 83767) (d := 143245)
    (by decide) h709155 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost354578 : endpointCostOK (354578, 393587, 251994) := by
  have h6150 := base_6150
  have h12300 : oddPrimeCount 12300 ≤ 1825 :=
    liftCount (m := 6150) (e := 12) (a := 800) (by decide) (by decide) (by decide) (by decide) (by decide) h6150
  have h24600 : oddPrimeCount 24600 ≤ 3717 :=
    liftCount (m := 12300) (e := 13) (a := 1825) (by decide) (by decide) (by decide) (by decide) (by decide) h12300
  have h49199 : oddPrimeCount 49199 ≤ 7231 :=
    liftCount (m := 24600) (e := 14) (a := 3717) (by decide) (by decide) (by decide) (by decide) (by decide) h24600
  have h98397 : oddPrimeCount 98397 ≤ 13790 :=
    liftCount (m := 49199) (e := 15) (a := 7231) (by decide) (by decide) (by decide) (by decide) (by decide) h49199
  have h196794 : oddPrimeCount 196794 ≤ 26089 :=
    liftCount (m := 98397) (e := 16) (a := 13790) (by decide) (by decide) (by decide) (by decide) (by decide) h98397
  have h393588 : oddPrimeCount 393588 ≤ 49241 :=
    liftCount (m := 196794) (e := 17) (a := 26089) (by decide) (by decide) (by decide) (by decide) (by decide) h196794
  have h787175 : oddPrimeCount 787175 ≤ 92973 :=
    liftCount (m := 393588) (e := 18) (a := 49241) (by decide) (by decide) (by decide) (by decide) (by decide) h393588
  exact endpointCost_of_parts (j := 393587) (a := 92973) (d := 159021)
    (by decide) h787175 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost393588 : endpointCostOK (393588, 436897, 279722) := by
  have h6827 := base_6827
  have h13654 : oddPrimeCount 13654 ≤ 2014 :=
    liftCount (m := 6827) (e := 12) (a := 877) (by decide) (by decide) (by decide) (by decide) (by decide) h6827
  have h27307 : oddPrimeCount 27307 ≤ 4114 :=
    liftCount (m := 13654) (e := 13) (a := 2014) (by decide) (by decide) (by decide) (by decide) (by decide) h13654
  have h54613 : oddPrimeCount 54613 ≤ 8015 :=
    liftCount (m := 27307) (e := 14) (a := 4114) (by decide) (by decide) (by decide) (by decide) (by decide) h27307
  have h109225 : oddPrimeCount 109225 ≤ 15296 :=
    liftCount (m := 54613) (e := 15) (a := 8015) (by decide) (by decide) (by decide) (by decide) (by decide) h54613
  have h218449 : oddPrimeCount 218449 ≤ 28949 :=
    liftCount (m := 109225) (e := 16) (a := 15296) (by decide) (by decide) (by decide) (by decide) (by decide) h109225
  have h436898 : oddPrimeCount 436898 ≤ 54648 :=
    liftCount (m := 218449) (e := 17) (a := 28949) (by decide) (by decide) (by decide) (by decide) (by decide) h218449
  have h873795 : oddPrimeCount 873795 ≤ 103192 :=
    liftCount (m := 436898) (e := 18) (a := 54648) (by decide) (by decide) (by decide) (by decide) (by decide) h436898
  exact endpointCost_of_parts (j := 436897) (a := 103192) (d := 176530)
    (by decide) h873795 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost436898 : endpointCostOK (436898, 484973, 310503) := by
  have h7578 := base_7578
  have h15156 : oddPrimeCount 15156 ≤ 2224 :=
    liftCount (m := 7578) (e := 12) (a := 961) (by decide) (by decide) (by decide) (by decide) (by decide) h7578
  have h30311 : oddPrimeCount 30311 ≤ 4555 :=
    liftCount (m := 15156) (e := 13) (a := 2224) (by decide) (by decide) (by decide) (by decide) (by decide) h15156
  have h60622 : oddPrimeCount 60622 ≤ 8885 :=
    liftCount (m := 30311) (e := 14) (a := 4555) (by decide) (by decide) (by decide) (by decide) (by decide) h30311
  have h121244 : oddPrimeCount 121244 ≤ 16967 :=
    liftCount (m := 60622) (e := 15) (a := 8885) (by decide) (by decide) (by decide) (by decide) (by decide) h60622
  have h242487 : oddPrimeCount 242487 ≤ 32122 :=
    liftCount (m := 121244) (e := 16) (a := 16967) (by decide) (by decide) (by decide) (by decide) (by decide) h121244
  have h484974 : oddPrimeCount 484974 ≤ 60649 :=
    liftCount (m := 242487) (e := 17) (a := 32122) (by decide) (by decide) (by decide) (by decide) (by decide) h242487
  have h969947 : oddPrimeCount 969947 ≤ 114535 :=
    liftCount (m := 484974) (e := 18) (a := 60649) (by decide) (by decide) (by decide) (by decide) (by decide) h484974
  exact endpointCost_of_parts (j := 484973) (a := 114535) (d := 195968)
    (by decide) h969947 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost484974 : endpointCostOK (484974, 553144, 346882) := by
  have h8643 := base_8643
  have h17286 : oddPrimeCount 17286 ≤ 2404 :=
    liftCount (m := 8643) (e := 13) (a := 1075) (by decide) (by decide) (by decide) (by decide) (by decide) h8643
  have h34572 : oddPrimeCount 34572 ≤ 4873 :=
    liftCount (m := 17286) (e := 14) (a := 2404) (by decide) (by decide) (by decide) (by decide) (by decide) h17286
  have h69144 : oddPrimeCount 69144 ≤ 9482 :=
    liftCount (m := 34572) (e := 15) (a := 4873) (by decide) (by decide) (by decide) (by decide) (by decide) h34572
  have h138287 : oddPrimeCount 138287 ≤ 18125 :=
    liftCount (m := 69144) (e := 16) (a := 9482) (by decide) (by decide) (by decide) (by decide) (by decide) h69144
  have h276573 : oddPrimeCount 276573 ≤ 34394 :=
    liftCount (m := 138287) (e := 17) (a := 18125) (by decide) (by decide) (by decide) (by decide) (by decide) h138287
  have h553145 : oddPrimeCount 553145 ≤ 65124 :=
    liftCount (m := 276573) (e := 18) (a := 34394) (by decide) (by decide) (by decide) (by decide) (by decide) h276573
  have h1106289 : oddPrimeCount 1106289 ≤ 123349 :=
    liftCount (m := 553145) (e := 19) (a := 65124) (by decide) (by decide) (by decide) (by decide) (by decide) h553145
  exact endpointCost_of_parts (j := 553144) (a := 123349) (d := 223533)
    (by decide) h1106289 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost553145 : endpointCostOK (553145, 630879, 395641) := by
  have h9858 := base_9858
  have h19715 : oddPrimeCount 19715 ≤ 2731 :=
    liftCount (m := 9858) (e := 13) (a := 1215) (by decide) (by decide) (by decide) (by decide) (by decide) h9858
  have h39430 : oddPrimeCount 39430 ≤ 5547 :=
    liftCount (m := 19715) (e := 14) (a := 2731) (by decide) (by decide) (by decide) (by decide) (by decide) h19715
  have h78860 : oddPrimeCount 78860 ≤ 10804 :=
    liftCount (m := 39430) (e := 15) (a := 5547) (by decide) (by decide) (by decide) (by decide) (by decide) h39430
  have h157720 : oddPrimeCount 157720 ≤ 20661 :=
    liftCount (m := 78860) (e := 16) (a := 10804) (by decide) (by decide) (by decide) (by decide) (by decide) h78860
  have h315440 : oddPrimeCount 315440 ≤ 39216 :=
    liftCount (m := 157720) (e := 17) (a := 20661) (by decide) (by decide) (by decide) (by decide) (by decide) h157720
  have h630880 : oddPrimeCount 630880 ≤ 74264 :=
    liftCount (m := 315440) (e := 18) (a := 39216) (by decide) (by decide) (by decide) (by decide) (by decide) h315440
  have h1261759 : oddPrimeCount 1261759 ≤ 140672 :=
    liftCount (m := 630880) (e := 19) (a := 74264) (by decide) (by decide) (by decide) (by decide) (by decide) h630880
  exact endpointCost_of_parts (j := 630879) (a := 140672) (d := 254969)
    (by decide) h1261759 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost630880 : endpointCostOK (630880, 718920, 451150) := by
  have h5617 := base_5617
  have h11234 : oddPrimeCount 11234 ≤ 1673 :=
    liftCount (m := 5617) (e := 12) (a := 737) (by decide) (by decide) (by decide) (by decide) (by decide) h5617
  have h22467 : oddPrimeCount 22467 ≤ 3401 :=
    liftCount (m := 11234) (e := 13) (a := 1673) (by decide) (by decide) (by decide) (by decide) (by decide) h11234
  have h44933 : oddPrimeCount 44933 ≤ 6610 :=
    liftCount (m := 22467) (e := 14) (a := 3401) (by decide) (by decide) (by decide) (by decide) (by decide) h22467
  have h89866 : oddPrimeCount 89866 ≤ 12601 :=
    liftCount (m := 44933) (e := 15) (a := 6610) (by decide) (by decide) (by decide) (by decide) (by decide) h44933
  have h179731 : oddPrimeCount 179731 ≤ 23834 :=
    liftCount (m := 89866) (e := 16) (a := 12601) (by decide) (by decide) (by decide) (by decide) (by decide) h89866
  have h359461 : oddPrimeCount 359461 ≤ 44978 :=
    liftCount (m := 179731) (e := 17) (a := 23834) (by decide) (by decide) (by decide) (by decide) (by decide) h179731
  have h718921 : oddPrimeCount 718921 ≤ 84918 :=
    liftCount (m := 359461) (e := 18) (a := 44978) (by decide) (by decide) (by decide) (by decide) (by decide) h359461
  have h1437841 : oddPrimeCount 1437841 ≤ 160593 :=
    liftCount (m := 718921) (e := 19) (a := 84918) (by decide) (by decide) (by decide) (by decide) (by decide) h718921
  exact endpointCost_of_parts (j := 718920) (a := 160593) (d := 290557)
    (by decide) h1437841 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost718921 : endpointCostOK (718921, 808306, 507256) := by
  have h6315 := base_6315
  have h12630 : oddPrimeCount 12630 ≤ 1872 :=
    liftCount (m := 6315) (e := 12) (a := 820) (by decide) (by decide) (by decide) (by decide) (by decide) h6315
  have h25260 : oddPrimeCount 25260 ≤ 3815 :=
    liftCount (m := 12630) (e := 13) (a := 1872) (by decide) (by decide) (by decide) (by decide) (by decide) h12630
  have h50520 : oddPrimeCount 50520 ≤ 7423 :=
    liftCount (m := 25260) (e := 14) (a := 3815) (by decide) (by decide) (by decide) (by decide) (by decide) h25260
  have h101039 : oddPrimeCount 101039 ≤ 14159 :=
    liftCount (m := 50520) (e := 15) (a := 7423) (by decide) (by decide) (by decide) (by decide) (by decide) h50520
  have h202077 : oddPrimeCount 202077 ≤ 26788 :=
    liftCount (m := 101039) (e := 16) (a := 14159) (by decide) (by decide) (by decide) (by decide) (by decide) h101039
  have h404154 : oddPrimeCount 404154 ≤ 50561 :=
    liftCount (m := 202077) (e := 17) (a := 26788) (by decide) (by decide) (by decide) (by decide) (by decide) h202077
  have h808307 : oddPrimeCount 808307 ≤ 95467 :=
    liftCount (m := 404154) (e := 18) (a := 50561) (by decide) (by decide) (by decide) (by decide) (by decide) h404154
  have h1616613 : oddPrimeCount 1616613 ≤ 180551 :=
    liftCount (m := 808307) (e := 19) (a := 95467) (by decide) (by decide) (by decide) (by decide) (by decide) h808307
  exact endpointCost_of_parts (j := 808306) (a := 180551) (d := 326705)
    (by decide) h1616613 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost808307 : endpointCostOK (808307, 879582, 551993) := by
  have h6872 := base_6872
  have h13744 : oddPrimeCount 13744 ≤ 2029 :=
    liftCount (m := 6872) (e := 12) (a := 884) (by decide) (by decide) (by decide) (by decide) (by decide) h6872
  have h27487 : oddPrimeCount 27487 ≤ 4143 :=
    liftCount (m := 13744) (e := 13) (a := 2029) (by decide) (by decide) (by decide) (by decide) (by decide) h13744
  have h54974 : oddPrimeCount 54974 ≤ 8069 :=
    liftCount (m := 27487) (e := 14) (a := 4143) (by decide) (by decide) (by decide) (by decide) (by decide) h27487
  have h109948 : oddPrimeCount 109948 ≤ 15398 :=
    liftCount (m := 54974) (e := 15) (a := 8069) (by decide) (by decide) (by decide) (by decide) (by decide) h54974
  have h219896 : oddPrimeCount 219896 ≤ 29141 :=
    liftCount (m := 109948) (e := 16) (a := 15398) (by decide) (by decide) (by decide) (by decide) (by decide) h109948
  have h439792 : oddPrimeCount 439792 ≤ 55011 :=
    liftCount (m := 219896) (e := 17) (a := 29141) (by decide) (by decide) (by decide) (by decide) (by decide) h219896
  have h879583 : oddPrimeCount 879583 ≤ 103876 :=
    liftCount (m := 439792) (e := 18) (a := 55011) (by decide) (by decide) (by decide) (by decide) (by decide) h439792
  have h1759165 : oddPrimeCount 1759165 ≤ 196463 :=
    liftCount (m := 879583) (e := 19) (a := 103876) (by decide) (by decide) (by decide) (by decide) (by decide) h879583
  exact endpointCost_of_parts (j := 879582) (a := 196463) (d := 355530)
    (by decide) h1759165 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost879583 : endpointCostOK (879583, 949526, 595878) := by
  have h7419 := base_7419
  have h14837 : oddPrimeCount 14837 ≤ 2176 :=
    liftCount (m := 7419) (e := 12) (a := 940) (by decide) (by decide) (by decide) (by decide) (by decide) h7419
  have h29673 : oddPrimeCount 29673 ≤ 4458 :=
    liftCount (m := 14837) (e := 13) (a := 2176) (by decide) (by decide) (by decide) (by decide) (by decide) h14837
  have h59346 : oddPrimeCount 59346 ≤ 8697 :=
    liftCount (m := 29673) (e := 14) (a := 4458) (by decide) (by decide) (by decide) (by decide) (by decide) h29673
  have h118691 : oddPrimeCount 118691 ≤ 16609 :=
    liftCount (m := 59346) (e := 15) (a := 8697) (by decide) (by decide) (by decide) (by decide) (by decide) h59346
  have h237382 : oddPrimeCount 237382 ≤ 31445 :=
    liftCount (m := 118691) (e := 16) (a := 16609) (by decide) (by decide) (by decide) (by decide) (by decide) h118691
  have h474764 : oddPrimeCount 474764 ≤ 59372 :=
    liftCount (m := 237382) (e := 17) (a := 31445) (by decide) (by decide) (by decide) (by decide) (by decide) h237382
  have h949527 : oddPrimeCount 949527 ≤ 112123 :=
    liftCount (m := 474764) (e := 18) (a := 59372) (by decide) (by decide) (by decide) (by decide) (by decide) h474764
  have h1899053 : oddPrimeCount 1899053 ≤ 212073 :=
    liftCount (m := 949527) (e := 19) (a := 112123) (by decide) (by decide) (by decide) (by decide) (by decide) h949527
  exact endpointCost_of_parts (j := 949526) (a := 212073) (d := 383805)
    (by decide) h1899053 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost949527 : endpointCostOK (949527, 1000000, 627559) := by
  have h7813 := base_7813
  have h15626 : oddPrimeCount 15626 ≤ 2288 :=
    liftCount (m := 7813) (e := 12) (a := 986) (by decide) (by decide) (by decide) (by decide) (by decide) h7813
  have h31251 : oddPrimeCount 31251 ≤ 4692 :=
    liftCount (m := 15626) (e := 13) (a := 2288) (by decide) (by decide) (by decide) (by decide) (by decide) h15626
  have h62501 : oddPrimeCount 62501 ≤ 9156 :=
    liftCount (m := 31251) (e := 14) (a := 4692) (by decide) (by decide) (by decide) (by decide) (by decide) h31251
  have h125001 : oddPrimeCount 125001 ≤ 17489 :=
    liftCount (m := 62501) (e := 15) (a := 9156) (by decide) (by decide) (by decide) (by decide) (by decide) h62501
  have h250001 : oddPrimeCount 250001 ≤ 33114 :=
    liftCount (m := 125001) (e := 16) (a := 17489) (by decide) (by decide) (by decide) (by decide) (by decide) h125001
  have h500001 : oddPrimeCount 500001 ≤ 62525 :=
    liftCount (m := 250001) (e := 17) (a := 33114) (by decide) (by decide) (by decide) (by decide) (by decide) h250001
  have h1000001 : oddPrimeCount 1000001 ≤ 118080 :=
    liftCount (m := 500001) (e := 18) (a := 62525) (by decide) (by decide) (by decide) (by decide) (by decide) h500001
  have h2000001 : oddPrimeCount 2000001 ≤ 223343 :=
    liftCount (m := 1000001) (e := 19) (a := 118080) (by decide) (by decide) (by decide) (by decide) (by decide) h1000001
  exact endpointCost_of_parts (j := 1000000) (a := 223343) (d := 404216)
    (by decide) h2000001 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem allCosts : ∀ c ∈ rows, endpointCostOK c := by
  unfold rows
  refine List.forall_mem_cons.mpr ⟨endpointCost300, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost308, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost315, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost324, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost333, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost342, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost356, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost369, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost386, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost410, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost431, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost455, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost485, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost518, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost551, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost593, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost644, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost711, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost783, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost866, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost965, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1083, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1229, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1401, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1625, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1886, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost2214, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost2502, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost2811, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost3176, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost3614, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost4154, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost4806, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5022, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5256, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5504, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost6059, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost6359, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost6695, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost7047, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost7448, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost7875, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost8547, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost9292, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost10000, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost10354, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost10731, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost11121, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost11530, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost11960, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost12416, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost12888, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost13388, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost13910, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost14456, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost15046, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost15658, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost16839, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost18122, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost19508, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost20488, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost21537, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost22635, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost23802, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost25034, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost26334, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost27716, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost29175, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost30718, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost32351, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost35264, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost38447, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost41392, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost42542, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost43672, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost44834, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost46028, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost47250, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost48202, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost49172, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost50167, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost51179, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost52216, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost53282, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost54374, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost55494, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost56628, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost57794, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost58987, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost60212, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost61458, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost62744, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost64061, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost67622, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost71393, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost75375, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost79583, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost83488, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost87584, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost91886, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost96415, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost101152, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost106142, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost111383, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost116888, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost122668, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost128744, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost139445, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost151038, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost163058, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost176049, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost190067, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost205209, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost221567, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost239252, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost258341, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost287262, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost319424, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost354578, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost393588, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost436898, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost484974, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost553145, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost630880, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost718921, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost808307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost879583, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost949527, ?_⟩
  simp

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

private def wholeError (r : ℕ) : ℕ := if r = 0 then 0 else 2^(r-1)

private lemma initialError_asNat (r : ℕ) :
    initialError r = (wholeError r : ℚ) := by
  by_cases h : r = 0 <;> simp [initialError, wholeError, h]

private def integralProfileChecks (lo hi : ℕ) (c : ℤ) : Prop :=
  ∀ A ∈ smallPrimes.powerset, ∀ t : Fin 5,
    (∏ p ∈ A, p)*19^t.val ≤ 2*hi+2 →
    let D := ∏ p ∈ A, p
    let P := ∏ p ∈ A, (p-1)
    let m := t.val
    (c - (refund hi A : ℤ) + (wholeError (A.card+m) : ℤ)) * (D : ℤ) * (19 : ℤ)^m <
      (lo : ℤ) * (P : ℤ) * (18 : ℤ)^m

private theorem profiles_of_integer {lo hi : ℕ} {c : ℤ}
    (he : integralProfileChecks lo hi c) : profileChecks lo hi c := by
  intro A hA t hfit
  let D := ∏ p ∈ A, p
  let P := ∏ p ∈ A, (p-1)
  let m := t.val
  have hint := he A hA t hfit
  change (c - (refund hi A : ℤ) + (wholeError (A.card+m) : ℤ)) * (D : ℤ) * (19 : ℤ)^m <
    (lo : ℤ) * (P : ℤ) * (18 : ℤ)^m at hint
  have hrat : ((c : ℚ) - (refund hi A : ℚ) + (wholeError (A.card+m) : ℚ)) *
      (D : ℚ) * (19 : ℚ)^m < (lo : ℚ) * (P : ℚ) * (18 : ℚ)^m := by
    exact_mod_cast hint
  have known : ∀ p ∈ smallPrimes, 2 < p := by decide
  have hs (p : ℕ) (hp : p ∈ A) : 2 < p := known p (Finset.mem_powerset.mp hA hp)
  have hDnat : 0 < D := Finset.prod_pos (fun p hp => by have := hs p hp; omega)
  have hD : (0 : ℚ) < D := by exact_mod_cast hDnat
  have hρ : largeRho A * (D : ℚ) = (P : ℚ) := by
    dsimp only [largeRho, D, P]
    simp only [Nat.cast_prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpos := hs p hp
    have hn : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
    field_simp [hn] <;> ring
  have hpower : (18/19 : ℚ)^m * (19 : ℚ)^m = (18 : ℚ)^m := by
    rw [← mul_pow]
    norm_num
  change (c : ℚ) - (refund hi A : ℚ) + initialError (A.card+m) <
    (lo : ℚ) * largeRho A * (18/19 : ℚ)^m
  apply (mul_lt_mul_iff_of_pos_right (mul_pos hD (by positivity : (0 : ℚ) < 19^m))).mp
  calc
    _ = ((c : ℚ) - (refund hi A : ℚ) + (wholeError (A.card+m) : ℚ)) *
        (D : ℚ) * (19 : ℚ)^m := by rw [initialError_asNat]; ring
    _ < _ := hrat
    _ = (lo : ℚ) * (largeRho A * (D : ℚ)) * ((18/19 : ℚ)^m * (19 : ℚ)^m) := by
      rw [hρ, hpower]
    _ = _ := by ring

private def verifiedRow (c : ℕ × ℕ × ℤ) : Prop :=
  300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧ integralProfileChecks c.1 c.2.1 c.2.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow300 : verifiedRow (300, 307, 227) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow308 : verifiedRow (308, 314, 231) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow315 : verifiedRow (315, 323, 238) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow324 : verifiedRow (324, 332, 244) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow333 : verifiedRow (333, 341, 251) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow342 : verifiedRow (342, 355, 259) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow356 : verifiedRow (356, 368, 269) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow369 : verifiedRow (369, 385, 280) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow386 : verifiedRow (386, 409, 293) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow410 : verifiedRow (410, 430, 312) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow431 : verifiedRow (431, 454, 327) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow455 : verifiedRow (455, 484, 347) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow485 : verifiedRow (485, 517, 371) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow518 : verifiedRow (518, 550, 396) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow551 : verifiedRow (551, 592, 422) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow593 : verifiedRow (593, 643, 454) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow644 : verifiedRow (644, 710, 494) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow711 : verifiedRow (711, 782, 546) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow783 : verifiedRow (783, 865, 605) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow866 : verifiedRow (866, 964, 669) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow965 : verifiedRow (965, 1082, 747) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1083 : verifiedRow (1083, 1228, 842) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1229 : verifiedRow (1229, 1400, 957) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1401 : verifiedRow (1401, 1624, 1093) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1625 : verifiedRow (1625, 1885, 1268) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1886 : verifiedRow (1886, 2213, 1477) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2214 : verifiedRow (2214, 2501, 1658) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2502 : verifiedRow (2502, 2810, 1852) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2811 : verifiedRow (2811, 3175, 2085) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow3176 : verifiedRow (3176, 3613, 2359) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow3614 : verifiedRow (3614, 4153, 2693) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow4154 : verifiedRow (4154, 4805, 3100) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow4806 : verifiedRow (4806, 5021, 3506) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5022 : verifiedRow (5022, 5255, 3667) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5256 : verifiedRow (5256, 5503, 3839) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5504 : verifiedRow (5504, 5770, 4022) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5771 : verifiedRow (5771, 6058, 4218) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6059 : verifiedRow (6059, 6358, 4428) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6359 : verifiedRow (6359, 6694, 4652) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6695 : verifiedRow (6695, 7046, 4897) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7047 : verifiedRow (7047, 7447, 5160) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7448 : verifiedRow (7448, 7874, 5454) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7875 : verifiedRow (7875, 8546, 5800) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow8547 : verifiedRow (8547, 9291, 6298) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow9292 : verifiedRow (9292, 9999, 6771) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow10000 : verifiedRow (10000, 10353, 7292) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow10354 : verifiedRow (10354, 10730, 7551) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow10731 : verifiedRow (10731, 11120, 7826) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow11121 : verifiedRow (11121, 11529, 8112) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow11530 : verifiedRow (11530, 11959, 8412) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow11960 : verifiedRow (11960, 12415, 8728) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow12416 : verifiedRow (12416, 12887, 9061) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow12888 : verifiedRow (12888, 13387, 9407) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow13388 : verifiedRow (13388, 13909, 9771) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow13910 : verifiedRow (13910, 14455, 10155) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow14456 : verifiedRow (14456, 15045, 10557) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow15046 : verifiedRow (15046, 15657, 10986) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow15658 : verifiedRow (15658, 16838, 11516) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow16839 : verifiedRow (16839, 18121, 12386) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow18122 : verifiedRow (18122, 19507, 13329) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow19508 : verifiedRow (19508, 20487, 14275) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow20488 : verifiedRow (20488, 21536, 14995) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow21537 : verifiedRow (21537, 22634, 15762) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow22635 : verifiedRow (22635, 23801, 16569) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow23802 : verifiedRow (23802, 25033, 17424) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow25034 : verifiedRow (25034, 26333, 18327) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow26334 : verifiedRow (26334, 27715, 19281) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow27716 : verifiedRow (27716, 29174, 20294) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow29175 : verifiedRow (29175, 30717, 21364) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow30718 : verifiedRow (30718, 32350, 22495) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow32351 : verifiedRow (32351, 35263, 23869) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow35264 : verifiedRow (35264, 38446, 26020) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow38447 : verifiedRow (38447, 41391, 28292) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow41392 : verifiedRow (41392, 42541, 29073) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow42542 : verifiedRow (42542, 43671, 29841) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow43672 : verifiedRow (43672, 44833, 30635) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow44834 : verifiedRow (44834, 46027, 31452) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow46028 : verifiedRow (46028, 47249, 32288) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow47250 : verifiedRow (47250, 48201, 32934) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow48202 : verifiedRow (48202, 49171, 33596) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow49172 : verifiedRow (49172, 50166, 34275) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow50167 : verifiedRow (50167, 51178, 34967) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow51179 : verifiedRow (51179, 52215, 35675) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow52216 : verifiedRow (52216, 53281, 36398) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow53282 : verifiedRow (53282, 54373, 37142) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow54374 : verifiedRow (54374, 55493, 37906) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow55494 : verifiedRow (55494, 56627, 38685) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow56628 : verifiedRow (56628, 57793, 39477) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow57794 : verifiedRow (57794, 58986, 40290) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow58987 : verifiedRow (58987, 60211, 41123) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow60212 : verifiedRow (60212, 61457, 41977) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow61458 : verifiedRow (61458, 62743, 42849) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow62744 : verifiedRow (62744, 64060, 43746) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow64061 : verifiedRow (64061, 67621, 44996) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow67622 : verifiedRow (67622, 71392, 47499) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow71393 : verifiedRow (71393, 75374, 50149) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow75375 : verifiedRow (75375, 79582, 52947) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow79583 : verifiedRow (79583, 83487, 55823) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow83488 : verifiedRow (83488, 87583, 58563) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow87584 : verifiedRow (87584, 91885, 61438) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow91886 : verifiedRow (91886, 96414, 64459) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow96415 : verifiedRow (96415, 101151, 67635) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow101152 : verifiedRow (101152, 106141, 70962) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow106142 : verifiedRow (106142, 111382, 74465) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow111383 : verifiedRow (111383, 116887, 78141) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow116888 : verifiedRow (116888, 122667, 82005) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow122668 : verifiedRow (122668, 128743, 86061) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow128744 : verifiedRow (128744, 139444, 90971) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow139445 : verifiedRow (139445, 151037, 98532) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow151038 : verifiedRow (151038, 163057, 106647) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow163058 : verifiedRow (163058, 176048, 115137) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow176049 : verifiedRow (176049, 190066, 124310) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow190067 : verifiedRow (190067, 205208, 134210) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow205209 : verifiedRow (205209, 221566, 144907) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow221567 : verifiedRow (221567, 239251, 156462) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow239252 : verifiedRow (239252, 258340, 168951) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow258341 : verifiedRow (258341, 287261, 183670) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow287262 : verifiedRow (287262, 319423, 204234) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow319424 : verifiedRow (319424, 354577, 227012) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow354578 : verifiedRow (354578, 393587, 251994) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow393588 : verifiedRow (393588, 436897, 279722) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow436898 : verifiedRow (436898, 484973, 310503) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow484974 : verifiedRow (484974, 553144, 346882) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow553145 : verifiedRow (553145, 630879, 395641) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow630880 : verifiedRow (630880, 718920, 451150) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow718921 : verifiedRow (718921, 808306, 507256) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow808307 : verifiedRow (808307, 879582, 551993) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow879583 : verifiedRow (879583, 949526, 595878) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow949527 : verifiedRow (949527, 1000000, 627559) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel


set_option maxRecDepth 20000 in
private theorem checks : ∀ c ∈ rows, 300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧
    integralProfileChecks c.1 c.2.1 c.2.2 := by
  change ∀ c ∈ rows, verifiedRow c
  unfold rows
  refine List.forall_mem_cons.mpr ⟨moderateRow300, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow308, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow315, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow324, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow333, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow342, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow356, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow369, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow386, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow410, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow431, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow455, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow485, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow518, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow551, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow593, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow644, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow711, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow783, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow866, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow965, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1083, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1229, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1401, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1625, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1886, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow2214, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow2502, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow2811, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow3176, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow3614, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow4154, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow4806, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5022, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5256, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5504, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6059, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6359, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6695, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7047, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7448, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7875, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow8547, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow9292, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10000, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10354, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10731, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow11121, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow11530, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow11960, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow12416, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow12888, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow13388, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow13910, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow14456, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow15046, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow15658, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow16839, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow18122, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow19508, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow20488, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow21537, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow22635, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow23802, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow25034, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow26334, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow27716, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow29175, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow30718, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow32351, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow35264, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow38447, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow41392, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow42542, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow43672, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow44834, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow46028, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow47250, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow48202, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow49172, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow50167, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow51179, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow52216, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow53282, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow54374, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow55494, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow56628, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow57794, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow58987, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow60212, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow61458, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow62744, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow64061, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow67622, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow71393, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow75375, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow79583, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow83488, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow87584, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow91886, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow96415, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow101152, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow106142, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow111383, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow116888, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow122668, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow128744, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow139445, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow151038, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow163058, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow176049, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow190067, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow205209, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow221567, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow239252, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow258341, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow287262, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow319424, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow354578, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow393588, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow436898, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow484974, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow553145, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow630880, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow718921, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow808307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow879583, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow949527, ?_⟩
  simp

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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem row_coverage : covers 300 rows := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem moderate_sieve_budget {J : ℕ} (hlo : 300 ≤ J) (hhi : J ≤ 1000000)
    {S : Finset ℕ} (hS : ∀ p ∈ S, 2 < p ∧ p.Prime) (hB : (∏ p ∈ S,p) ≤ 2*J+2) :
    ∃ c ∈ rows, (((∑ p ∈ largePrimeSet (2*c.2.1+1), (2*c.2.1/(p^2)+1)) : ℕ) : ℤ) ≤ c.2.2 →
    ((∑ p ∈ largePrimeSet (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
        (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) < (J:ℚ)*largeRho S := by
  obtain ⟨c,hc,hl,hu⟩ := covers_mem hlo hhi row_coverage
  refine ⟨c,hc,?_⟩
  intro htotal
  obtain ⟨hl₀,hu₀,hiChecks⟩ := checks c hc
  have hcases := profiles_of_integer hiChecks
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
    have cast_bound (v : ℕ) (z : ℤ) (h : (v : ℤ) ≤ z) : (v : ℚ) ≤ (z : ℚ) := by
      have hc : ((v : ℤ) : ℚ) ≤ (z : ℚ) := Int.cast_le.mpr h
      simpa only [Int.cast_natCast] using hc
    simpa only [Nat.cast_add] using cast_bound _ _ hsumZ
  change _ + initialError S.card < _
  rw [← card]
  exact (add_le_add hleft le_rfl).trans_lt (hcase.trans_le hright)

end A085265Moderate

theorem OMA.solution : OMA.R_oeis_a085265_R2_H2_R1_H1_R1.H1 := by
  intro J S hlo hhi hS hB
  obtain ⟨c,hc,proof⟩ := A085265Moderate.moderate_sieve_budget hlo hhi hS hB
  exact proof (A085265Moderate.allCosts c hc)

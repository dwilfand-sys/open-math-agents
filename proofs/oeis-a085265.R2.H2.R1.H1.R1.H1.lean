import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1
import Mathlib

/-! The uniform finite sieve budget. The shared theorem retains the extra unit needed for A085267.
Proof by Codex for @dwilfand-sys. Root A085265 statement by @niclorusso. -/

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
private theorem smallCountTo605 : oddPrimeCount 605 = 109 :=
  smallPrimeAdvance 576 29 104 5 smallCountTo576 (by decide +kernel)

theorem base_605 : oddPrimeCount 605 ≤ 109 :=
  (smallCountTo605).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo611 : oddPrimeCount 611 = 110 :=
  smallPrimeAdvance 605 6 109 1 smallCountTo605 (by decide +kernel)

theorem base_611 : oddPrimeCount 611 ≤ 110 :=
  (smallCountTo611).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo615 : oddPrimeCount 615 = 111 :=
  smallPrimeAdvance 611 4 110 1 smallCountTo611 (by decide +kernel)

theorem base_615 : oddPrimeCount 615 ≤ 111 :=
  (smallCountTo615).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo617 : oddPrimeCount 617 = 112 :=
  smallPrimeAdvance 615 2 111 1 smallCountTo615 (by decide +kernel)

theorem base_617 : oddPrimeCount 617 ≤ 112 :=
  (smallCountTo617).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo629 : oddPrimeCount 629 = 113 :=
  smallPrimeAdvance 617 12 112 1 smallCountTo617 (by decide +kernel)

theorem base_629 : oddPrimeCount 629 ≤ 113 :=
  (smallCountTo629).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo641 : oddPrimeCount 641 = 115 :=
  smallPrimeAdvance 629 12 113 2 smallCountTo629 (by decide +kernel)

theorem base_641 : oddPrimeCount 641 ≤ 115 :=
  (smallCountTo641).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo651 : oddPrimeCount 651 = 117 :=
  smallPrimeAdvance 641 10 115 2 smallCountTo641 (by decide +kernel)

theorem base_651 : oddPrimeCount 651 ≤ 117 :=
  (smallCountTo651).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo659 : oddPrimeCount 659 = 119 :=
  smallPrimeAdvance 651 8 117 2 smallCountTo651 (by decide +kernel)

theorem base_659 : oddPrimeCount 659 ≤ 119 :=
  (smallCountTo659).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo671 : oddPrimeCount 671 = 120 :=
  smallPrimeAdvance 659 12 119 1 smallCountTo659 (by decide +kernel)

theorem base_671 : oddPrimeCount 671 ≤ 120 :=
  (smallCountTo671).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo681 : oddPrimeCount 681 = 122 :=
  smallPrimeAdvance 671 10 120 2 smallCountTo671 (by decide +kernel)

theorem base_681 : oddPrimeCount 681 ≤ 122 :=
  (smallCountTo681).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo699 : oddPrimeCount 699 = 124 :=
  smallPrimeAdvance 681 18 122 2 smallCountTo681 (by decide +kernel)

theorem base_699 : oddPrimeCount 699 ≤ 124 :=
  (smallCountTo699).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo731 : oddPrimeCount 731 = 128 :=
  smallPrimeAdvance 699 32 124 4 smallCountTo699 (by decide +kernel)

theorem base_731 : oddPrimeCount 731 ≤ 128 :=
  (smallCountTo731).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo759 : oddPrimeCount 759 = 133 :=
  smallPrimeAdvance 731 28 128 5 smallCountTo731 (by decide +kernel)

theorem base_759 : oddPrimeCount 759 ≤ 133 :=
  (smallCountTo759).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo809 : oddPrimeCount 809 = 139 :=
  smallPrimeAdvance 759 50 133 6 smallCountTo759 (by decide +kernel)

theorem base_809 : oddPrimeCount 809 ≤ 139 :=
  (smallCountTo809).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo841 : oddPrimeCount 841 = 145 :=
  smallPrimeAdvance 809 32 139 6 smallCountTo809 (by decide +kernel)

theorem base_841 : oddPrimeCount 841 ≤ 145 :=
  (smallCountTo841).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo881 : oddPrimeCount 881 = 151 :=
  smallPrimeAdvance 841 40 145 6 smallCountTo841 (by decide +kernel)

theorem base_881 : oddPrimeCount 881 ≤ 151 :=
  (smallCountTo881).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo939 : oddPrimeCount 939 = 158 :=
  smallPrimeAdvance 881 58 151 7 smallCountTo881 (by decide +kernel)

theorem base_939 : oddPrimeCount 939 ≤ 158 :=
  (smallCountTo939).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1003 : oddPrimeCount 1003 = 167 :=
  smallPrimeAdvance 939 64 158 9 smallCountTo939 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1017 : oddPrimeCount 1017 = 169 :=
  smallPrimeAdvance 1003 14 167 2 smallCountTo1003 (by decide +kernel)

theorem base_1017 : oddPrimeCount 1017 ≤ 169 :=
  (smallCountTo1017).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1081 : oddPrimeCount 1081 = 179 :=
  smallPrimeAdvance 1017 64 169 10 smallCountTo1017 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1101 : oddPrimeCount 1101 = 183 :=
  smallPrimeAdvance 1081 20 179 4 smallCountTo1081 (by decide +kernel)

theorem base_1101 : oddPrimeCount 1101 ≤ 183 :=
  (smallCountTo1101).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1165 : oddPrimeCount 1165 = 191 :=
  smallPrimeAdvance 1101 64 183 8 smallCountTo1101 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1199 : oddPrimeCount 1199 = 195 :=
  smallPrimeAdvance 1165 34 191 4 smallCountTo1165 (by decide +kernel)

theorem base_1199 : oddPrimeCount 1199 ≤ 195 :=
  (smallCountTo1199).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1263 : oddPrimeCount 1263 = 204 :=
  smallPrimeAdvance 1199 64 195 9 smallCountTo1199 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1327 : oddPrimeCount 1327 = 216 :=
  smallPrimeAdvance 1263 64 204 12 smallCountTo1263 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1359 : oddPrimeCount 1359 = 216 :=
  smallPrimeAdvance 1327 32 216 0 smallCountTo1327 (by decide +kernel)

theorem base_1359 : oddPrimeCount 1359 ≤ 216 :=
  (smallCountTo1359).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1423 : oddPrimeCount 1423 = 223 :=
  smallPrimeAdvance 1359 64 216 7 smallCountTo1359 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1487 : oddPrimeCount 1487 = 235 :=
  smallPrimeAdvance 1423 64 223 12 smallCountTo1423 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1551 : oddPrimeCount 1551 = 243 :=
  smallPrimeAdvance 1487 64 235 8 smallCountTo1487 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1557 : oddPrimeCount 1557 = 244 :=
  smallPrimeAdvance 1551 6 243 1 smallCountTo1551 (by decide +kernel)

theorem base_1557 : oddPrimeCount 1557 ≤ 244 :=
  (smallCountTo1557).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1621 : oddPrimeCount 1621 = 256 :=
  smallPrimeAdvance 1557 64 244 12 smallCountTo1557 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1685 : oddPrimeCount 1685 = 262 :=
  smallPrimeAdvance 1621 64 256 6 smallCountTo1621 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1749 : oddPrimeCount 1749 = 271 :=
  smallPrimeAdvance 1685 64 262 9 smallCountTo1685 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1813 : oddPrimeCount 1813 = 279 :=
  smallPrimeAdvance 1749 64 271 8 smallCountTo1749 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1829 : oddPrimeCount 1829 = 280 :=
  smallPrimeAdvance 1813 16 279 1 smallCountTo1813 (by decide +kernel)

theorem base_1829 : oddPrimeCount 1829 ≤ 280 :=
  (smallCountTo1829).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1893 : oddPrimeCount 1893 = 289 :=
  smallPrimeAdvance 1829 64 280 9 smallCountTo1829 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1957 : oddPrimeCount 1957 = 296 :=
  smallPrimeAdvance 1893 64 289 7 smallCountTo1893 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2021 : oddPrimeCount 2021 = 305 :=
  smallPrimeAdvance 1957 64 296 9 smallCountTo1957 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2047 : oddPrimeCount 2047 = 308 :=
  smallPrimeAdvance 2021 26 305 3 smallCountTo2021 (by decide +kernel)

theorem base_2047 : oddPrimeCount 2047 ≤ 308 :=
  (smallCountTo2047).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2111 : oddPrimeCount 2111 = 317 :=
  smallPrimeAdvance 2047 64 308 9 smallCountTo2047 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2175 : oddPrimeCount 2175 = 325 :=
  smallPrimeAdvance 2111 64 317 8 smallCountTo2111 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2239 : oddPrimeCount 2239 = 332 :=
  smallPrimeAdvance 2175 64 325 7 smallCountTo2175 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2303 : oddPrimeCount 2303 = 341 :=
  smallPrimeAdvance 2239 64 332 9 smallCountTo2239 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2367 : oddPrimeCount 2367 = 349 :=
  smallPrimeAdvance 2303 64 341 8 smallCountTo2303 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2421 : oddPrimeCount 2421 = 358 :=
  smallPrimeAdvance 2367 54 349 9 smallCountTo2367 (by decide +kernel)

theorem base_2421 : oddPrimeCount 2421 ≤ 358 :=
  (smallCountTo2421).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2485 : oddPrimeCount 2485 = 366 :=
  smallPrimeAdvance 2421 64 358 8 smallCountTo2421 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2549 : oddPrimeCount 2549 = 372 :=
  smallPrimeAdvance 2485 64 366 6 smallCountTo2485 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2613 : oddPrimeCount 2613 = 378 :=
  smallPrimeAdvance 2549 64 372 6 smallCountTo2549 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2677 : oddPrimeCount 2677 = 387 :=
  smallPrimeAdvance 2613 64 378 9 smallCountTo2613 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2741 : oddPrimeCount 2741 = 399 :=
  smallPrimeAdvance 2677 64 387 12 smallCountTo2677 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2805 : oddPrimeCount 2805 = 408 :=
  smallPrimeAdvance 2741 64 399 9 smallCountTo2741 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2869 : oddPrimeCount 2869 = 415 :=
  smallPrimeAdvance 2805 64 408 7 smallCountTo2805 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2933 : oddPrimeCount 2933 = 422 :=
  smallPrimeAdvance 2869 64 415 7 smallCountTo2869 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2951 : oddPrimeCount 2951 = 423 :=
  smallPrimeAdvance 2933 18 422 1 smallCountTo2933 (by decide +kernel)

theorem base_2951 : oddPrimeCount 2951 ≤ 423 :=
  (smallCountTo2951).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3015 : oddPrimeCount 3015 = 431 :=
  smallPrimeAdvance 2951 64 423 8 smallCountTo2951 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3079 : oddPrimeCount 3079 = 439 :=
  smallPrimeAdvance 3015 64 431 8 smallCountTo3015 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3143 : oddPrimeCount 3143 = 445 :=
  smallPrimeAdvance 3079 64 439 6 smallCountTo3079 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3207 : oddPrimeCount 3207 = 452 :=
  smallPrimeAdvance 3143 64 445 7 smallCountTo3143 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3271 : oddPrimeCount 3271 = 461 :=
  smallPrimeAdvance 3207 64 452 9 smallCountTo3207 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3335 : oddPrimeCount 3335 = 469 :=
  smallPrimeAdvance 3271 64 461 8 smallCountTo3271 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3399 : oddPrimeCount 3399 = 477 :=
  smallPrimeAdvance 3335 64 469 8 smallCountTo3335 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3463 : oddPrimeCount 3463 = 484 :=
  smallPrimeAdvance 3399 64 477 7 smallCountTo3399 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3527 : oddPrimeCount 3527 = 491 :=
  smallPrimeAdvance 3463 64 484 7 smallCountTo3463 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3591 : oddPrimeCount 3591 = 501 :=
  smallPrimeAdvance 3527 64 491 10 smallCountTo3527 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3655 : oddPrimeCount 3655 = 509 :=
  smallPrimeAdvance 3591 64 501 8 smallCountTo3591 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3707 : oddPrimeCount 3707 = 516 :=
  smallPrimeAdvance 3655 52 509 7 smallCountTo3655 (by decide +kernel)

theorem base_3707 : oddPrimeCount 3707 ≤ 516 :=
  (smallCountTo3707).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3771 : oddPrimeCount 3771 = 524 :=
  smallPrimeAdvance 3707 64 516 8 smallCountTo3707 (by decide +kernel)

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
private theorem smallCountTo4095 : oddPrimeCount 4095 = 563 :=
  smallPrimeAdvance 4091 4 562 1 smallCountTo4091 (by decide +kernel)

theorem base_4095 : oddPrimeCount 4095 ≤ 563 :=
  (smallCountTo4095).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4159 : oddPrimeCount 4159 = 572 :=
  smallPrimeAdvance 4095 64 563 9 smallCountTo4095 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4223 : oddPrimeCount 4223 = 577 :=
  smallPrimeAdvance 4159 64 572 5 smallCountTo4159 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4287 : oddPrimeCount 4287 = 587 :=
  smallPrimeAdvance 4223 64 577 10 smallCountTo4223 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4351 : oddPrimeCount 4351 = 593 :=
  smallPrimeAdvance 4287 64 587 6 smallCountTo4287 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4407 : oddPrimeCount 4407 = 598 :=
  smallPrimeAdvance 4351 56 593 5 smallCountTo4351 (by decide +kernel)

theorem base_4407 : oddPrimeCount 4407 ≤ 598 :=
  (smallCountTo4407).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4471 : oddPrimeCount 4471 = 606 :=
  smallPrimeAdvance 4407 64 598 8 smallCountTo4407 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4535 : oddPrimeCount 4535 = 614 :=
  smallPrimeAdvance 4471 64 606 8 smallCountTo4471 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4599 : oddPrimeCount 4599 = 621 :=
  smallPrimeAdvance 4535 64 614 7 smallCountTo4535 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4663 : oddPrimeCount 4663 = 630 :=
  smallPrimeAdvance 4599 64 621 9 smallCountTo4599 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4727 : oddPrimeCount 4727 = 636 :=
  smallPrimeAdvance 4663 64 630 6 smallCountTo4663 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4791 : oddPrimeCount 4791 = 643 :=
  smallPrimeAdvance 4727 64 636 7 smallCountTo4727 (by decide +kernel)

theorem base_4791 : oddPrimeCount 4791 ≤ 643 :=
  (smallCountTo4791).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4855 : oddPrimeCount 4855 = 649 :=
  smallPrimeAdvance 4791 64 643 6 smallCountTo4791 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4919 : oddPrimeCount 4919 = 656 :=
  smallPrimeAdvance 4855 64 649 7 smallCountTo4855 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4983 : oddPrimeCount 4983 = 665 :=
  smallPrimeAdvance 4919 64 656 9 smallCountTo4919 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5047 : oddPrimeCount 5047 = 674 :=
  smallPrimeAdvance 4983 64 665 9 smallCountTo4983 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5111 : oddPrimeCount 5111 = 682 :=
  smallPrimeAdvance 5047 64 674 8 smallCountTo5047 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5175 : oddPrimeCount 5175 = 688 :=
  smallPrimeAdvance 5111 64 682 6 smallCountTo5111 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5239 : oddPrimeCount 5239 = 696 :=
  smallPrimeAdvance 5175 64 688 8 smallCountTo5175 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5279 : oddPrimeCount 5279 = 699 :=
  smallPrimeAdvance 5239 40 696 3 smallCountTo5239 (by decide +kernel)

theorem base_5279 : oddPrimeCount 5279 ≤ 699 :=
  (smallCountTo5279).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5343 : oddPrimeCount 5343 = 705 :=
  smallPrimeAdvance 5279 64 699 6 smallCountTo5279 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5407 : oddPrimeCount 5407 = 712 :=
  smallPrimeAdvance 5343 64 705 7 smallCountTo5343 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5471 : oddPrimeCount 5471 = 721 :=
  smallPrimeAdvance 5407 64 712 9 smallCountTo5407 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5535 : oddPrimeCount 5535 = 731 :=
  smallPrimeAdvance 5471 64 721 10 smallCountTo5471 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5599 : oddPrimeCount 5599 = 737 :=
  smallPrimeAdvance 5535 64 731 6 smallCountTo5535 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5663 : oddPrimeCount 5663 = 745 :=
  smallPrimeAdvance 5599 64 737 8 smallCountTo5599 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5727 : oddPrimeCount 5727 = 752 :=
  smallPrimeAdvance 5663 64 745 7 smallCountTo5663 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5791 : oddPrimeCount 5791 = 759 :=
  smallPrimeAdvance 5727 64 752 7 smallCountTo5727 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5855 : oddPrimeCount 5855 = 768 :=
  smallPrimeAdvance 5791 64 759 9 smallCountTo5791 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5865 : oddPrimeCount 5865 = 770 :=
  smallPrimeAdvance 5855 10 768 2 smallCountTo5855 (by decide +kernel)

theorem base_5865 : oddPrimeCount 5865 ≤ 770 :=
  (smallCountTo5865).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5929 : oddPrimeCount 5929 = 778 :=
  smallPrimeAdvance 5865 64 770 8 smallCountTo5865 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5993 : oddPrimeCount 5993 = 782 :=
  smallPrimeAdvance 5929 64 778 4 smallCountTo5929 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6057 : oddPrimeCount 6057 = 789 :=
  smallPrimeAdvance 5993 64 782 7 smallCountTo5993 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6121 : oddPrimeCount 6121 = 797 :=
  smallPrimeAdvance 6057 64 789 8 smallCountTo6057 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6185 : oddPrimeCount 6185 = 803 :=
  smallPrimeAdvance 6121 64 797 6 smallCountTo6121 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6249 : oddPrimeCount 6249 = 811 :=
  smallPrimeAdvance 6185 64 803 8 smallCountTo6185 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6313 : oddPrimeCount 6313 = 820 :=
  smallPrimeAdvance 6249 64 811 9 smallCountTo6249 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6377 : oddPrimeCount 6377 = 830 :=
  smallPrimeAdvance 6313 64 820 10 smallCountTo6313 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6441 : oddPrimeCount 6441 = 835 :=
  smallPrimeAdvance 6377 64 830 5 smallCountTo6377 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6505 : oddPrimeCount 6505 = 841 :=
  smallPrimeAdvance 6441 64 835 6 smallCountTo6441 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6569 : oddPrimeCount 6569 = 848 :=
  smallPrimeAdvance 6505 64 841 7 smallCountTo6505 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6633 : oddPrimeCount 6633 = 854 :=
  smallPrimeAdvance 6569 64 848 6 smallCountTo6569 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6657 : oddPrimeCount 6657 = 856 :=
  smallPrimeAdvance 6633 24 854 2 smallCountTo6633 (by decide +kernel)

theorem base_6657 : oddPrimeCount 6657 ≤ 856 :=
  (smallCountTo6657).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6721 : oddPrimeCount 6721 = 866 :=
  smallPrimeAdvance 6657 64 856 10 smallCountTo6657 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6785 : oddPrimeCount 6785 = 872 :=
  smallPrimeAdvance 6721 64 866 6 smallCountTo6721 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6849 : oddPrimeCount 6849 = 880 :=
  smallPrimeAdvance 6785 64 872 8 smallCountTo6785 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6913 : oddPrimeCount 6913 = 888 :=
  smallPrimeAdvance 6849 64 880 8 smallCountTo6849 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6977 : oddPrimeCount 6977 = 896 :=
  smallPrimeAdvance 6913 64 888 8 smallCountTo6913 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7041 : oddPrimeCount 7041 = 904 :=
  smallPrimeAdvance 6977 64 896 8 smallCountTo6977 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7105 : oddPrimeCount 7105 = 909 :=
  smallPrimeAdvance 7041 64 904 5 smallCountTo7041 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7169 : oddPrimeCount 7169 = 915 :=
  smallPrimeAdvance 7105 64 909 6 smallCountTo7105 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7233 : oddPrimeCount 7233 = 923 :=
  smallPrimeAdvance 7169 64 915 8 smallCountTo7169 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7297 : oddPrimeCount 7297 = 929 :=
  smallPrimeAdvance 7233 64 923 6 smallCountTo7233 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7361 : oddPrimeCount 7361 = 936 :=
  smallPrimeAdvance 7297 64 929 7 smallCountTo7297 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7425 : oddPrimeCount 7425 = 940 :=
  smallPrimeAdvance 7361 64 936 4 smallCountTo7361 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7489 : oddPrimeCount 7489 = 948 :=
  smallPrimeAdvance 7425 64 940 8 smallCountTo7425 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7553 : oddPrimeCount 7553 = 957 :=
  smallPrimeAdvance 7489 64 948 9 smallCountTo7489 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7617 : oddPrimeCount 7617 = 966 :=
  smallPrimeAdvance 7553 64 957 9 smallCountTo7553 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7679 : oddPrimeCount 7679 = 972 :=
  smallPrimeAdvance 7617 62 966 6 smallCountTo7617 (by decide +kernel)

theorem base_7679 : oddPrimeCount 7679 ≤ 972 :=
  (smallCountTo7679).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7743 : oddPrimeCount 7743 = 981 :=
  smallPrimeAdvance 7679 64 972 9 smallCountTo7679 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7807 : oddPrimeCount 7807 = 986 :=
  smallPrimeAdvance 7743 64 981 5 smallCountTo7743 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7871 : oddPrimeCount 7871 = 992 :=
  smallPrimeAdvance 7807 64 986 6 smallCountTo7807 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7935 : oddPrimeCount 7935 = 1001 :=
  smallPrimeAdvance 7871 64 992 9 smallCountTo7871 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7999 : oddPrimeCount 7999 = 1006 :=
  smallPrimeAdvance 7935 64 1001 5 smallCountTo7935 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8063 : oddPrimeCount 8063 = 1012 :=
  smallPrimeAdvance 7999 64 1006 6 smallCountTo7999 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8127 : oddPrimeCount 8127 = 1021 :=
  smallPrimeAdvance 8063 64 1012 9 smallCountTo8063 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8191 : oddPrimeCount 8191 = 1027 :=
  smallPrimeAdvance 8127 64 1021 6 smallCountTo8127 (by decide +kernel)

theorem base_8191 : oddPrimeCount 8191 ≤ 1027 :=
  (smallCountTo8191).le

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
  · exact ⟨300,420,(183/500:ℚ),(96911/500000:ℚ),by decide,by omega,by omega⟩
  by_cases until_599 : J ≤ 599
  · exact ⟨421,599,(9/25:ℚ),(49013/250000:ℚ),by decide,by omega,by omega⟩
  by_cases until_1023 : J ≤ 1023
  · exact ⟨600,1023,(9/25:ℚ),(98959/500000:ℚ),by decide,by omega,by omega⟩
  by_cases until_2047 : J ≤ 2047
  · exact ⟨1024,2047,(7/20:ℚ),(199283/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_4095 : J ≤ 4095
  · exact ⟨2048,4095,(73/250:ℚ),(200323/1000000:ℚ),by decide,by omega,by omega⟩
  by_cases until_8191 : J ≤ 8191
  · exact ⟨4096,8191,(3127/10000:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  by_cases until_16383 : J ≤ 16383
  · exact ⟨8192,16383,(3103/10000:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  by_cases until_32767 : J ≤ 32767
  · exact ⟨16384,32767,(2981/10000:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  by_cases until_65535 : J ≤ 65535
  · exact ⟨32768,65535,(353/1250:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  by_cases until_131071 : J ≤ 131071
  · exact ⟨65536,131071,(2663/10000:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  by_cases until_262143 : J ≤ 262143
  · exact ⟨131072,262143,(627/2500:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  by_cases until_524287 : J ≤ 524287
  · exact ⟨262144,524287,(1183/5000:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩
  exact ⟨524288,1000000,(559/2500:ℚ),(41/200:ℚ),by decide,by omega,by omega⟩

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
    ((∑ p ∈ oddPrimes (2*J+1) \ S, 2*J/(p^2)+1 : ℕ) : ℚ) ≤
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
  change ((∑ p ∈ E, 2*J/(p^2)+1 : ℕ) : ℚ) ≤ _
  rw [sum_add_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_add]
  calc
    _ ≤ 2*(J:ℚ)*(R-recip A) + (α*(J:ℚ)-(A.card:ℚ)) :=
      add_le_add hf (by linarith only [csum])
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
      _ ≤ 1/(p : ℚ)^2 + 1/(2*(((p+1 : ℕ) : ℚ))) := add_le_add_left htail _
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

theorem OMA.solution : OMA.R_oeis_a085265_R2_H2_R1_H1_R1.H1 := by
  intro J S hlo hhi hS hB
  have strong := A085267.SameJ.Assembly.budget hlo hhi hS hB
  apply lt_of_le_of_lt ?_ strong
  apply add_le_add_left
  exact le_add_of_nonneg_left (by norm_num)

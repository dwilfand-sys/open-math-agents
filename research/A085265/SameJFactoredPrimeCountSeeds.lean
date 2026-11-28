import Mathlib

/-!
# Odd-prime upper bounds at 35 squarefree-sieve endpoints

Each composite in the finite intervals is certified by a proper divisor packed in
base 128. The upper bound is all that the analytic sieve needs.
Credit: @dwilfand-sys. These endpoints serve OEIS A085265 and A085267.
-/

namespace A085265.DyadicPrimeCount

open Finset

def oddPrimesUpTo (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter (fun p => 2 < p ∧ p.Prime)

def oddPrimeCount (x : ℕ) : ℕ := (oddPrimesUpTo x).card

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

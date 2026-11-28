import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R4
import Mathlib

/-!
# Exact odd-prime counts at 242 finite endpoints

Credit: @dwilfand-sys. The original A085265 statement was formalized by
@niclorusso. The endpoints support two squarefree representation sieves.
Intervals are disjoint, have at most 64 members, and cover 1 through 10000.
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
private theorem smallCountTo611 : oddPrimeCount 611 ≤ 110 :=
  smallPrimeAdvanceUpper 576 35 104 6 0x103041c10b040c100044c1030400105040c10004001030414100040c10d
    smallCountTo576 (by decide +kernel)

theorem base_611 : oddPrimeCount 611 ≤ 110 := smallCountTo611

set_option maxRecDepth 10000 in
private theorem smallCountTo615 : oddPrimeCount 615 ≤ 111 :=
  smallPrimeAdvanceUpper 611 4 110 1 0x400103
    smallCountTo611 (by decide +kernel)

theorem base_615 : oddPrimeCount 615 ≤ 111 := smallCountTo615

set_option maxRecDepth 10000 in
private theorem smallCountTo621 : oddPrimeCount 621 ≤ 113 :=
  smallPrimeAdvanceUpper 615 6 111 2 0x1000400103
    smallCountTo615 (by decide +kernel)

theorem base_621 : oddPrimeCount 621 ≤ 113 := smallCountTo621

set_option maxRecDepth 10000 in
private theorem smallCountTo629 : oddPrimeCount 629 ≤ 113 :=
  smallPrimeAdvanceUpper 621 8 113 0 0x41c105040c111
    smallCountTo621 (by decide +kernel)

theorem base_629 : oddPrimeCount 629 ≤ 113 := smallCountTo629

set_option maxRecDepth 10000 in
private theorem smallCountTo639 : oddPrimeCount 639 ≤ 114 :=
  smallPrimeAdvanceUpper 629 10 113 1 0x100040c105041c103
    smallCountTo629 (by decide +kernel)

theorem base_639 : oddPrimeCount 639 ≤ 114 := smallCountTo639

set_option maxRecDepth 10000 in
private theorem smallCountTo647 : oddPrimeCount 647 ≤ 117 :=
  smallPrimeAdvanceUpper 639 8 114 3 0x400100040c100
    smallCountTo639 (by decide +kernel)

theorem base_647 : oddPrimeCount 647 ≤ 117 := smallCountTo647

set_option maxRecDepth 10000 in
private theorem smallCountTo657 : oddPrimeCount 657 ≤ 118 :=
  smallPrimeAdvanceUpper 647 10 117 1 0x10b040c1000414103
    smallCountTo647 (by decide +kernel)

theorem base_657 : oddPrimeCount 657 ≤ 118 := smallCountTo657

set_option maxRecDepth 10000 in
private theorem smallCountTo665 : oddPrimeCount 665 ≤ 120 :=
  smallPrimeAdvanceUpper 657 8 118 2 0x400100040c105
    smallCountTo657 (by decide +kernel)

theorem base_665 : oddPrimeCount 665 ≤ 120 := smallCountTo665

set_option maxRecDepth 10000 in
private theorem smallCountTo675 : oddPrimeCount 675 ≤ 121 :=
  smallPrimeAdvanceUpper 665 10 120 1 0x117040c10b0400103
    smallCountTo665 (by decide +kernel)

theorem base_675 : oddPrimeCount 675 ≤ 121 := smallCountTo675

set_option maxRecDepth 10000 in
private theorem smallCountTo683 : oddPrimeCount 683 ≤ 123 :=
  smallPrimeAdvanceUpper 675 8 121 2 0x400107040c100
    smallCountTo675 (by decide +kernel)

theorem base_683 : oddPrimeCount 683 ≤ 123 := smallCountTo683

set_option maxRecDepth 10000 in
private theorem smallCountTo693 : oddPrimeCount 693 ≤ 124 :=
  smallPrimeAdvanceUpper 683 10 123 1 0x105040c10d0400103
    smallCountTo683 (by decide +kernel)

theorem base_693 : oddPrimeCount 693 ≤ 124 := smallCountTo693

set_option maxRecDepth 10000 in
private theorem smallCountTo711 : oddPrimeCount 711 ≤ 126 :=
  smallPrimeAdvanceUpper 693 18 124 2 0x10504441030400113040c1070400103
    smallCountTo693 (by decide +kernel)

theorem base_711 : oddPrimeCount 711 ≤ 126 := smallCountTo711

set_option maxRecDepth 10000 in
private theorem smallCountTo719 : oddPrimeCount 719 ≤ 127 :=
  smallPrimeAdvanceUpper 711 8 126 1 0x45c105040c100
    smallCountTo711 (by decide +kernel)

theorem base_719 : oddPrimeCount 719 ≤ 127 := smallCountTo719

set_option maxRecDepth 10000 in
private theorem smallCountTo737 : oddPrimeCount 737 ≤ 129 :=
  smallPrimeAdvanceUpper 719 18 127 2 0x107040c10504001030444100040c10b
    smallCountTo719 (by decide +kernel)

theorem base_737 : oddPrimeCount 737 ≤ 129 := smallCountTo737

set_option maxRecDepth 10000 in
private theorem smallCountTo747 : oddPrimeCount 747 ≤ 131 :=
  smallPrimeAdvanceUpper 737 10 129 2 0x100040c1000414103
    smallCountTo737 (by decide +kernel)

theorem base_747 : oddPrimeCount 747 ≤ 131 := smallCountTo747

set_option maxRecDepth 10000 in
private theorem smallCountTo771 : oddPrimeCount 771 ≤ 135 :=
  smallPrimeAdvanceUpper 747 24 131 4 0x41c100040c10504001030400107040c10d0400103
    smallCountTo747 (by decide +kernel)

theorem base_771 : oddPrimeCount 771 ≤ 135 := smallCountTo771

set_option maxRecDepth 10000 in
private theorem smallCountTo783 : oddPrimeCount 783 ≤ 136 :=
  smallPrimeAdvanceUpper 771 12 135 1 0x400105040c113042c103
    smallCountTo771 (by decide +kernel)

theorem base_783 : oddPrimeCount 783 ≤ 136 := smallCountTo783

set_option maxRecDepth 10000 in
private theorem smallCountTo819 : oddPrimeCount 819 ≤ 140 :=
  smallPrimeAdvanceUpper 783 36 136 4 0x414100040c10704341030400111040c10b04141030400100040c105044c103
    smallCountTo783 (by decide +kernel)

theorem base_819 : oddPrimeCount 819 ≤ 140 := smallCountTo819

set_option maxRecDepth 10000 in
private theorem smallCountTo825 : oddPrimeCount 825 ≤ 142 :=
  smallPrimeAdvanceUpper 819 6 140 2 0x1000400103
    smallCountTo819 (by decide +kernel)

theorem base_825 : oddPrimeCount 825 ≤ 142 := smallCountTo825

set_option maxRecDepth 10000 in
private theorem smallCountTo861 : oddPrimeCount 861 ≤ 148 :=
  smallPrimeAdvanceUpper 825 36 142 6 0x400100040c1070414103040011d040c105041c103045c100040c1000400103
    smallCountTo825 (by decide +kernel)

theorem base_861 : oddPrimeCount 861 ≤ 148 := smallCountTo861

set_option maxRecDepth 10000 in
private theorem smallCountTo863 : oddPrimeCount 863 ≤ 149 :=
  smallPrimeAdvanceUpper 861 2 148 1 0x100
    smallCountTo861 (by decide +kernel)

theorem base_863 : oddPrimeCount 863 ≤ 149 := smallCountTo863

set_option maxRecDepth 10000 in
private theorem smallCountTo909 : oddPrimeCount 909 ≤ 154 :=
  smallPrimeAdvanceUpper 863 46 149 5 0x105040c10b04341030414100040c10004001030400107040c11304141030474111040c1050400103
    smallCountTo863 (by decide +kernel)

theorem base_909 : oddPrimeCount 909 ≤ 154 := smallCountTo909

set_option maxRecDepth 10000 in
private theorem smallCountTo965 : oddPrimeCount 965 ≤ 161 :=
  smallPrimeAdvanceUpper 909 56 154 7 0x40010b040c10704001030434105040c100041c1030414100040c100045c103040010d040c1000414103041c11f040c105
    smallCountTo909 (by decide +kernel)

theorem base_965 : oddPrimeCount 965 ≤ 161 := smallCountTo965

set_option maxRecDepth 10000 in
private theorem smallCountTo969 : oddPrimeCount 969 ≤ 162 :=
  smallPrimeAdvanceUpper 965 4 161 1 0x400103
    smallCountTo965 (by decide +kernel)

theorem base_969 : oddPrimeCount 969 ≤ 162 := smallCountTo969

set_option maxRecDepth 10000 in
private theorem smallCountTo1029 : oddPrimeCount 1029 ≤ 171 :=
  smallPrimeAdvanceUpper 969 60 162 9 0x400107040c100042c1030400105040c11704001030414100040c1070444103044c100040c10004141030400100040c1050434103
    smallCountTo969 (by decide +kernel)

theorem base_1029 : oddPrimeCount 1029 ≤ 171 := smallCountTo1029

set_option maxRecDepth 10000 in
private theorem smallCountTo1035 : oddPrimeCount 1035 ≤ 173 :=
  smallPrimeAdvanceUpper 1029 6 171 2 0x1000400103
    smallCountTo1029 (by decide +kernel)

theorem base_1035 : oddPrimeCount 1035 ≤ 173 := smallCountTo1035

set_option maxRecDepth 10000 in
private theorem smallCountTo1095 : oddPrimeCount 1095 ≤ 182 :=
  smallPrimeAdvanceUpper 1035 60 173 9 0x444100040c10704141030400100040c105041c1030400100040c10b04001030474105040c10d045c1030414100040c1000400103
    smallCountTo1035 (by decide +kernel)

theorem base_1095 : oddPrimeCount 1095 ≤ 182 := smallCountTo1095

set_option maxRecDepth 10000 in
private theorem smallCountTo1101 : oddPrimeCount 1101 ≤ 183 :=
  smallPrimeAdvanceUpper 1095 6 182 1 0x100041c103
    smallCountTo1095 (by decide +kernel)

theorem base_1101 : oddPrimeCount 1101 ≤ 183 := smallCountTo1101

set_option maxRecDepth 10000 in
private theorem smallCountTo1165 : oddPrimeCount 1165 ≤ 191 :=
  smallPrimeAdvanceUpper 1101 64 183 8 0x400105040c100042c1030414100040c1130400103041c100040c10b04141030444107040c105047c1030400100040c10d044c1030400105
    smallCountTo1101 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1179 : oddPrimeCount 1179 ≤ 192 :=
  smallPrimeAdvanceUpper 1165 14 191 1 0x103041c100040c105042c103
    smallCountTo1165 (by decide +kernel)

theorem base_1179 : oddPrimeCount 1179 ≤ 192 := smallCountTo1179

set_option maxRecDepth 10000 in
private theorem smallCountTo1185 : oddPrimeCount 1185 ≤ 193 :=
  smallPrimeAdvanceUpper 1179 6 192 1 0x100041c103
    smallCountTo1179 (by decide +kernel)

theorem base_1185 : oddPrimeCount 1185 ≤ 193 := smallCountTo1185

set_option maxRecDepth 10000 in
private theorem smallCountTo1249 : oddPrimeCount 1249 ≤ 203 :=
  smallPrimeAdvanceUpper 1185 64 193 10 0x40011d040c1000414103042c100040c1050444103041c100040c100045c1030400105040c10004001030414100040c111042c1030474100
    smallCountTo1185 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1277 : oddPrimeCount 1277 ≤ 205 :=
  smallPrimeAdvanceUpper 1249 28 203 2 0x40c1070414103040010d040c105041c103047c113040c100
    smallCountTo1249 (by decide +kernel)

theorem base_1277 : oddPrimeCount 1277 ≤ 205 := smallCountTo1277

set_option maxRecDepth 10000 in
private theorem smallCountTo1287 : oddPrimeCount 1287 ≤ 207 :=
  smallPrimeAdvanceUpper 1277 10 205 2 0x100040c1000414103
    smallCountTo1277 (by decide +kernel)

theorem base_1287 : oddPrimeCount 1287 ≤ 207 := smallCountTo1287

set_option maxRecDepth 10000 in
private theorem smallCountTo1351 : oddPrimeCount 1351 ≤ 216 :=
  smallPrimeAdvanceUpper 1287 64 207 9 0x400100040c10504001030400100040c100041c1030434105040c10004001030414100040c10b047c103041c10d040c1110414103044c107
    smallCountTo1287 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1403 : oddPrimeCount 1403 ≤ 221 :=
  smallPrimeAdvanceUpper 1351 52 216 5 0x40c105045c103040011d040c10004941030400105040c10704001030414113040c10d041c103042c100040c117
    smallCountTo1351 (by decide +kernel)

theorem base_1403 : oddPrimeCount 1403 ≤ 221 := smallCountTo1403

set_option maxRecDepth 10000 in
private theorem smallCountTo1421 : oddPrimeCount 1421 ≤ 222 :=
  smallPrimeAdvanceUpper 1403 18 221 1 0x105040c1000444103041410d040c107
    smallCountTo1403 (by decide +kernel)

theorem base_1421 : oddPrimeCount 1421 ≤ 222 := smallCountTo1421

set_option maxRecDepth 10000 in
private theorem smallCountTo1485 : oddPrimeCount 1485 ≤ 234 :=
  smallPrimeAdvanceUpper 1421 64 222 12 0x4001030400100040c1000414103040010b040c10504001030400100040c11f0400103041c105040c10d04001030414107040c1000400103
    smallCountTo1421 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1541 : oddPrimeCount 1541 ≤ 241 :=
  smallPrimeAdvanceUpper 1485 56 234 7 0x400100040c10004141030400113040c105042c1030400111040c125041c1030400105040c10b0400103041411d040c117
    smallCountTo1485 (by decide +kernel)

theorem base_1541 : oddPrimeCount 1541 ≤ 241 := smallCountTo1541

set_option maxRecDepth 10000 in
private theorem smallCountTo1565 : oddPrimeCount 1565 ≤ 245 :=
  smallPrimeAdvanceUpper 1541 24 241 4 0x400103041c100040c10004141030400107040c105
    smallCountTo1541 (by decide +kernel)

theorem base_1565 : oddPrimeCount 1565 ≤ 245 := smallCountTo1565

set_option maxRecDepth 10000 in
private theorem smallCountTo1629 : oddPrimeCount 1629 ≤ 257 :=
  smallPrimeAdvanceUpper 1565 64 245 12 0x400103040010b040c11304001030400105040c10704941030414100040c100041c1030400100040c10004141030400100040c1050400103
    smallCountTo1565 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1693 : oddPrimeCount 1693 ≤ 263 :=
  smallPrimeAdvanceUpper 1629 64 257 6 0x41c117040c100042c103047c105040c11104341030414100040c10b04001030400100040c1070414103045c129040c105041c103044c100
    smallCountTo1629 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1695 : oddPrimeCount 1695 ≤ 263 :=
  smallPrimeAdvanceUpper 1693 2 263 0 0x103
    smallCountTo1693 (by decide +kernel)

theorem base_1695 : oddPrimeCount 1695 ≤ 263 := smallCountTo1695

set_option maxRecDepth 10000 in
private theorem smallCountTo1731 : oddPrimeCount 1731 ≤ 268 :=
  smallPrimeAdvanceUpper 1695 36 263 5 0x400100040c10d0414103040011d040c10504441030400100040c10b041c103
    smallCountTo1695 (by decide +kernel)

theorem base_1731 : oddPrimeCount 1731 ≤ 268 := smallCountTo1731

set_option maxRecDepth 10000 in
private theorem smallCountTo1795 : oddPrimeCount 1795 ≤ 277 :=
  smallPrimeAdvanceUpper 1731 64 268 9 0x400105040c12504001030414100040c1110400103041c100040c12904141030474107040c10504001030434100040c1000400103042c105
    smallCountTo1731 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1859 : oddPrimeCount 1859 ≤ 282 :=
  smallPrimeAdvanceUpper 1795 64 277 5 0x40c1070400103041410d040c100041c103045c111040c1000414103047c100040c105042c103041c113040c10004ac1030444105040c10b
    smallCountTo1795 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo1877 : oddPrimeCount 1877 ≤ 287 :=
  smallPrimeAdvanceUpper 1859 18 282 5 0x100040c10504001030400100040c100
    smallCountTo1859 (by decide +kernel)

theorem base_1877 : oddPrimeCount 1877 ≤ 287 := smallCountTo1877

set_option maxRecDepth 10000 in
private theorem smallCountTo1929 : oddPrimeCount 1929 ≤ 292 :=
  smallPrimeAdvanceUpper 1877 52 287 5 0x400103041c105040c100047c1030414107040c100042c1030400117040c1000414103044c111040c10504a4103
    smallCountTo1877 (by decide +kernel)

theorem base_1929 : oddPrimeCount 1929 ≤ 292 := smallCountTo1929

set_option maxRecDepth 10000 in
private theorem smallCountTo1993 : oddPrimeCount 1993 ≤ 300 :=
  smallPrimeAdvanceUpper 1929 64 292 8 0x400100040c10d041c1030474105040c10004001030414113040c1250434103041c10b040c10004141030400107040c1050400103042c100
    smallCountTo1929 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2057 : oddPrimeCount 2057 ≤ 309 :=
  smallPrimeAdvanceUpper 1993 64 300 9 0x40c10004001030400105040c10704001030414100040c12b041c1030400100040c1130414103040010d040c105045c103041c100040c10b
    smallCountTo1993 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2105 : oddPrimeCount 2105 ≤ 316 :=
  smallPrimeAdvanceUpper 2057 48 309 7 0x4741030400105040c100044c103041411f040c10004001030400100040c1070414103040010b040c105
    smallCountTo2057 (by decide +kernel)

theorem base_2105 : oddPrimeCount 2105 ≤ 316 := smallCountTo2105

set_option maxRecDepth 10000 in
private theorem smallCountTo2165 : oddPrimeCount 2165 ≤ 325 :=
  smallPrimeAdvanceUpper 2105 60 316 9 0x41c1030400100040c11d0434103042c105040c10004001030414100040c1000400103044c107040c10004141030444100040c105
    smallCountTo2105 (by decide +kernel)

theorem base_2165 : oddPrimeCount 2165 ≤ 325 := smallCountTo2165

set_option maxRecDepth 10000 in
private theorem smallCountTo2229 : oddPrimeCount 2229 ≤ 330 :=
  smallPrimeAdvanceUpper 2165 64 325 5 0x42c1030434129040c10704001030494105040c10b041c103041410d040c11f0400103040012f040c1000414103041c100040c1050444103
    smallCountTo2165 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2293 : oddPrimeCount 2293 ≤ 340 :=
  smallPrimeAdvanceUpper 2229 64 330 10 0x45c107040c10004001030400105040c10d04001030414125040c107047c1030400100040c100041410304ac100040c10504001030474100
    smallCountTo2229 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2357 : oddPrimeCount 2357 ≤ 349 :=
  smallPrimeAdvanceUpper 2293 64 340 9 0x40c100042c103041c105040c10004001030414107040c10b045c1030434111040c10004141030400100040c1050400103040010d040c100
    smallCountTo2293 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2375 : oddPrimeCount 2375 ≤ 350 :=
  smallPrimeAdvanceUpper 2357 18 349 1 0x107040c1110414103045c100040c105
    smallCountTo2357 (by decide +kernel)

theorem base_2375 : oddPrimeCount 2375 ≤ 350 := smallCountTo2375

set_option maxRecDepth 10000 in
private theorem smallCountTo2439 : oddPrimeCount 2439 ≤ 360 :=
  smallPrimeAdvanceUpper 2375 64 350 10 0x4001030400100040c10704001030400105040c100041c103041411d040c100044c1030400129040c1000414103041c10b040c1050400103
    smallCountTo2375 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2457 : oddPrimeCount 2457 ≤ 362 :=
  smallPrimeAdvanceUpper 2439 18 360 2 0x100041c103040011f040c10b0414103
    smallCountTo2439 (by decide +kernel)

theorem base_2457 : oddPrimeCount 2457 ≤ 362 := smallCountTo2457

set_option maxRecDepth 10000 in
private theorem smallCountTo2521 : oddPrimeCount 2521 ≤ 368 :=
  smallPrimeAdvanceUpper 2457 64 362 6 0x400117040c1050400103041c100040c10004941030434105040c11304bc103041410b040c1290400103045c10d040c1070414103042c100
    smallCountTo2457 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2585 : oddPrimeCount 2585 ≤ 375 :=
  smallPrimeAdvanceUpper 2521 64 368 7 0x40c105041c1030400111040c12b04001030400105040c10004001030414100040c10d042c1030444107040c11f0414103040011d040c105
    smallCountTo2521 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2649 : oddPrimeCount 2649 ≤ 382 :=
  smallPrimeAdvanceUpper 2585 64 375 7 0x4341030400100040c107045c103044c105040c100041c1030414100040c10004ac103049410b040c1000414103041c113040c1050400103
    smallCountTo2585 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2705 : oddPrimeCount 2705 ≤ 392 :=
  smallPrimeAdvanceUpper 2649 56 382 10 0x42c107040c10004001030400105040c11104001030414100040c10704001030400100040c10004141030400125040c105
    smallCountTo2649 (by decide +kernel)

theorem base_2705 : oddPrimeCount 2705 ≤ 392 := smallCountTo2705

set_option maxRecDepth 10000 in
private theorem smallCountTo2769 : oddPrimeCount 2769 ≤ 402 :=
  smallPrimeAdvanceUpper 2705 64 392 10 0x4001030400100040c10b0400103041c105040c10004001030414107040c100043410304a4100040c1000414103047c10b040c1050400103
    smallCountTo2705 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2801 : oddPrimeCount 2801 ≤ 407 :=
  smallPrimeAdvanceUpper 2769 32 402 5 0x44412f040c100041c103042c105040c10004001030414100040c100
    smallCountTo2769 (by decide +kernel)

theorem base_2801 : oddPrimeCount 2801 ≤ 407 := smallCountTo2801

set_option maxRecDepth 10000 in
private theorem smallCountTo2865 : oddPrimeCount 2865 ≤ 415 :=
  smallPrimeAdvanceUpper 2801 64 407 8 0x400103041c135040c11d04141030400107040c105042c103044c100040c10004441030400105040c10704001030414100040c100041c103
    smallCountTo2801 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2929 : oddPrimeCount 2929 ≤ 422 :=
  smallPrimeAdvanceUpper 2865 64 415 7 0x4bc113040c10d0414103040012b040c1050400103041c10b040c10004341030400105040c10004a41030414100040c1170494103040011d
    smallCountTo2865 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo2993 : oddPrimeCount 2993 ≤ 428 :=
  smallPrimeAdvanceUpper 2929 64 422 6 0x40c10704141030400111040c105041c1030434100040c100042c1030400105040c1000400103041410d040c10b044c1030474107040c129
    smallCountTo2929 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3057 : oddPrimeCount 3057 ≤ 436 :=
  smallPrimeAdvanceUpper 2993 64 428 8 0x4141030400100040c105047c1030400117040c10704001030400105040c10d041c1030414100040c1000444103042c100040c12b0414103
    smallCountTo2993 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3117 : oddPrimeCount 3117 ≤ 442 :=
  smallPrimeAdvanceUpper 3057 60 436 6 0x41c100040c10504001030494107040c11104001030400105040c100042c1030414113040c10704741030434100040c10b0414103
    smallCountTo3057 (by decide +kernel)

theorem base_3117 : oddPrimeCount 3117 ≤ 442 := smallCountTo3117

set_option maxRecDepth 10000 in
private theorem smallCountTo3181 : oddPrimeCount 3181 ≤ 449 :=
  smallPrimeAdvanceUpper 3117 64 442 7 0x400100040c10504d4103047c10d040c10004ac103041c105040c12f045c1030414107040c11d04001030400100040c1130414103042c100
    smallCountTo3117 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3245 : oddPrimeCount 3245 ≤ 456 :=
  smallPrimeAdvanceUpper 3181 64 449 7 0x40c1050400103040011f040c117041c1030400105040c10004341030414100040c100042c103041c100040c135041410304a4107040c105
    smallCountTo3181 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3249 : oddPrimeCount 3249 ≤ 456 :=
  smallPrimeAdvanceUpper 3245 4 456 0 0x444103
    smallCountTo3245 (by decide +kernel)

theorem base_3249 : oddPrimeCount 3249 ≤ 456 := smallCountTo3249

set_option maxRecDepth 10000 in
private theorem smallCountTo3313 : oddPrimeCount 3313 ≤ 465 :=
  smallPrimeAdvanceUpper 3249 64 456 9 0x400100040c10004001030434105040c1070400103041411d040c111041c103044c10b040c12504141030400100040c1050400103041c100
    smallCountTo3249 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3377 : oddPrimeCount 3377 ≤ 475 :=
  smallPrimeAdvanceUpper 3313 64 465 10 0x40c11f04001030400105040c1000400103041412f040c10d04001030400111040c10704141030400100040c105041c1030400100040c10b
    smallCountTo3313 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3441 : oddPrimeCount 3441 ≤ 480 :=
  smallPrimeAdvanceUpper 3377 64 475 5 0x47c1030444105040c1000400103041412b040c11304a41030400107040c1000414103043410b040c105045c10304bc100040c107044c103
    smallCountTo3377 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3505 : oddPrimeCount 3505 ≤ 488 :=
  smallPrimeAdvanceUpper 3441 64 480 8 0x42c105040c100041c1030414100040c10004001030400100040c1170414103041c13b040c105042c1030400107040c10d0400103047c105
    smallCountTo3441 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3569 : oddPrimeCount 3569 ≤ 498 :=
  smallPrimeAdvanceUpper 3505 64 488 10 0x40c10b04001030414100040c10704341030400100040c10004141030400100040c105040010304d410b040c1000400103041c105040c12b
    smallCountTo3505 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3615 : oddPrimeCount 3615 ≤ 504 :=
  smallPrimeAdvanceUpper 3569 46 498 6 0x100040c105041c1030400100040c11104941030400105040c13b04341030414100040c1170400103
    smallCountTo3569 (by decide +kernel)

theorem base_3615 : oddPrimeCount 3615 ≤ 504 := smallCountTo3615

set_option maxRecDepth 10000 in
private theorem smallCountTo3679 : oddPrimeCount 3679 ≤ 513 :=
  smallPrimeAdvanceUpper 3615 64 504 9 0x400107040c1000414103044c100040c1050400103042c100040c10704a41030434105040c100041c1030414113040c1000400103040010d
    smallCountTo3615 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3743 : oddPrimeCount 3743 ≤ 521 :=
  smallPrimeAdvanceUpper 3679 64 513 8 0x40c11d0414103041c100040c10504001030400107040c10b040010304bc105040c10004f41030414100040c10704001030494100040c113
    smallCountTo3679 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo3771 : oddPrimeCount 3771 ≤ 524 :=
  smallPrimeAdvanceUpper 3743 28 521 3 0x414103045c10b040c10504341030400135040c1000400103
    smallCountTo3743 (by decide +kernel)

theorem base_3771 : oddPrimeCount 3771 ≤ 524 := smallCountTo3771

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
private theorem smallCountTo4155 : oddPrimeCount 4155 ≤ 570 :=
  smallPrimeAdvanceUpper 4091 64 562 8 0x4001030444100040c10b0414103041c100040c105045c1030434107040c10004001030400105040c10004a4103041410b040c1070400103
    smallCountTo4091 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4219 : oddPrimeCount 4219 ≤ 577 :=
  smallPrimeAdvanceUpper 4155 64 570 7 0x400100040c1170414103042c12b040c1050400103049412f040c13504ec103041c105040c10d04001030414107040c100042c1030400100
    smallCountTo4155 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4229 : oddPrimeCount 4229 ≤ 578 :=
  smallPrimeAdvanceUpper 4219 10 577 1 0x10304a4105040c100
    smallCountTo4219 (by decide +kernel)

theorem base_4229 : oddPrimeCount 4229 ≤ 578 := smallCountTo4229

set_option maxRecDepth 10000 in
private theorem smallCountTo4293 : oddPrimeCount 4293 ≤ 588 :=
  smallPrimeAdvanceUpper 4229 64 578 10 0x4001030414113040c1000400103047c107040c10004141030400100040c10504441030400100040c107042c1030400105040c100041c103
    smallCountTo4229 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4357 : oddPrimeCount 4357 ≤ 594 :=
  smallPrimeAdvanceUpper 4293 64 588 6 0x414100040c10b043410304ec11f040c1130414103041c11d040c105040010304f4107040c100040010304ac105040c100044c1030414100
    smallCountTo4293 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4421 : oddPrimeCount 4421 ≤ 600 :=
  smallPrimeAdvanceUpper 4357 64 594 6 0x40c1070400103042c111040c1000414103047410d040c10504a41030400117040c10004d4103041c105040c100042c1030414107040c100
    smallCountTo4357 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4427 : oddPrimeCount 4427 ≤ 601 :=
  smallPrimeAdvanceUpper 4421 6 600 1 0x100040c113
    smallCountTo4421 (by decide +kernel)

theorem base_4427 : oddPrimeCount 4427 ≤ 601 := smallCountTo4427

set_option maxRecDepth 10000 in
private theorem smallCountTo4491 : oddPrimeCount 4491 ≤ 608 :=
  smallPrimeAdvanceUpper 4427 64 601 7 0x4ac103042c105040c11704001030414100040c10004f41030400107040c100041410304a4111040c105042c1030400100040c107050c103
    smallCountTo4427 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4555 : oddPrimeCount 4555 ≤ 616 :=
  smallPrimeAdvanceUpper 4491 64 608 8 0x400105040c10b041c1030414100040c10d04001030400100040c1000414103041c117040c1050434103044c107040c10004001030474105
    smallCountTo4491 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4619 : oddPrimeCount 4619 ≤ 622 :=
  smallPrimeAdvanceUpper 4555 64 616 6 0x40c12f04001030414100040c1070444103045c113040c10004141030434100040c105040010304ac100040c111042c103041c105040c11f
    smallCountTo4555 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4683 : oddPrimeCount 4683 ≤ 632 :=
  smallPrimeAdvanceUpper 4619 64 622 10 0x4001030414107040c10b04a41030400100040c10004141030400100040c105040010304ec100040c10d041c1030400105040c100047c103
    smallCountTo4619 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4747 : oddPrimeCount 4747 ≤ 638 :=
  smallPrimeAdvanceUpper 4683 64 632 6 0x41412b040c1000434103041c125040c10004141030444107040c10504d41030400100040c11d04001030400105040c107042c103041412f
    smallCountTo4683 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4811 : oddPrimeCount 4811 ≤ 646 :=
  smallPrimeAdvanceUpper 4747 64 638 8 0x40c100041c103050c100040c10b0414103044c10d040c1050444103041c100040c10004001030400105040c1000400103041410b040c111
    smallCountTo4747 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4875 : oddPrimeCount 4875 ≤ 651 :=
  smallPrimeAdvanceUpper 4811 64 646 5 0x400103040013d040c1070414103042c100040c105041c10304bc11d040c1250434103045c105040c12b0400103041411f040c100042c103
    smallCountTo4811 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo4939 : oddPrimeCount 4939 ≤ 659 :=
  smallPrimeAdvanceUpper 4875 64 651 8 0x400107040c11304141030400143040c10504ec1030434100040c10704001030444105040c100041c103041410d040c1000400103040010b
    smallCountTo4875 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5003 : oddPrimeCount 5003 ≤ 669 :=
  smallPrimeAdvanceUpper 4939 64 659 10 0x40c1000414103041c100040c1050400103042c107040c10004001030400105040c10d04441030414100040c1070400103044c100040c100
    smallCountTo4939 (by decide +kernel)

theorem base_5003 : oddPrimeCount 5003 ≤ 669 := smallCountTo5003

set_option maxRecDepth 10000 in
private theorem smallCountTo5013 : oddPrimeCount 5013 ≤ 671 :=
  smallPrimeAdvanceUpper 5003 10 669 2 0x105040c1000400103
    smallCountTo5003 (by decide +kernel)

theorem base_5013 : oddPrimeCount 5013 ≤ 671 := smallCountTo5013

set_option maxRecDepth 10000 in
private theorem smallCountTo5022 : oddPrimeCount 5022 ≤ 672 :=
  smallPrimeAdvanceUpper 5013 9 671 1 0x20a08e820608002
    smallCountTo5013 (by decide +kernel)

theorem base_5022 : oddPrimeCount 5022 ≤ 672 := smallCountTo5022

set_option maxRecDepth 10000 in
private theorem smallCountTo5057 : oddPrimeCount 5057 ≤ 675 :=
  smallPrimeAdvanceUpper 5022 35 672 3 0x103042c12f040c10704141030400147040c105041c103040011f040c10d
    smallCountTo5022 (by decide +kernel)

theorem base_5057 : oddPrimeCount 5057 ≤ 675 := smallCountTo5057

set_option maxRecDepth 10000 in
private theorem smallCountTo5091 : oddPrimeCount 5091 ≤ 679 :=
  smallPrimeAdvanceUpper 5057 34 675 4 0x100040c13d0414103049410b040c1050400103040010d040c100041c103
    smallCountTo5057 (by decide +kernel)

theorem base_5091 : oddPrimeCount 5091 ≤ 679 := smallCountTo5091

set_option maxRecDepth 10000 in
private theorem smallCountTo5096 : oddPrimeCount 5096 ≤ 679 :=
  smallPrimeAdvanceUpper 5091 5 679 0 0x21608282
    smallCountTo5091 (by decide +kernel)

theorem base_5096 : oddPrimeCount 5096 ≤ 679 := smallCountTo5096

set_option maxRecDepth 10000 in
private theorem smallCountTo5110 : oddPrimeCount 5110 ≤ 682 :=
  smallPrimeAdvanceUpper 5096 14 679 3 0x182000800206082820008182
    smallCountTo5096 (by decide +kernel)

theorem base_5110 : oddPrimeCount 5110 ≤ 682 := smallCountTo5110

set_option maxRecDepth 10000 in
private theorem smallCountTo5122 : oddPrimeCount 5122 ≤ 684 :=
  smallPrimeAdvanceUpper 5110 12 682 2 0x260800206083820008182
    smallCountTo5110 (by decide +kernel)

theorem base_5122 : oddPrimeCount 5122 ≤ 684 := smallCountTo5122

set_option maxRecDepth 10000 in
private theorem smallCountTo5125 : oddPrimeCount 5125 ≤ 684 :=
  smallPrimeAdvanceUpper 5122 3 684 0 0xbc105
    smallCountTo5122 (by decide +kernel)

theorem base_5125 : oddPrimeCount 5125 ≤ 684 := smallCountTo5125

set_option maxRecDepth 10000 in
private theorem smallCountTo5156 : oddPrimeCount 5156 ≤ 686 :=
  smallPrimeAdvanceUpper 5125 31 684 2 0x81822e08382060828216081826a09282060800226081820008282
    smallCountTo5125 (by decide +kernel)

theorem base_5156 : oddPrimeCount 5156 ≤ 686 := smallCountTo5156

set_option maxRecDepth 10000 in
private theorem smallCountTo5174 : oddPrimeCount 5174 ≤ 688 :=
  smallPrimeAdvanceUpper 5156 18 686 2 0x1820e08682060828200081820008382
    smallCountTo5156 (by decide +kernel)

theorem base_5174 : oddPrimeCount 5174 ≤ 688 := smallCountTo5174

set_option maxRecDepth 10000 in
private theorem smallCountTo5177 : oddPrimeCount 5177 ≤ 688 :=
  smallPrimeAdvanceUpper 5174 3 688 0 0xc11f
    smallCountTo5174 (by decide +kernel)

theorem base_5177 : oddPrimeCount 5177 ≤ 688 := smallCountTo5177

set_option maxRecDepth 10000 in
private theorem smallCountTo5213 : oddPrimeCount 5213 ≤ 692 :=
  smallPrimeAdvanceUpper 5177 36 688 4 0x400103051c105040c10004741030414100040c107042c10304a4100040c10d
    smallCountTo5177 (by decide +kernel)

theorem base_5213 : oddPrimeCount 5213 ≤ 692 := smallCountTo5213

set_option maxRecDepth 10000 in
private theorem smallCountTo5218 : oddPrimeCount 5218 ≤ 692 :=
  smallPrimeAdvanceUpper 5213 5 692 0 0x20a08182
    smallCountTo5213 (by decide +kernel)

theorem base_5218 : oddPrimeCount 5218 ≤ 692 := smallCountTo5218

set_option maxRecDepth 10000 in
private theorem smallCountTo5243 : oddPrimeCount 5243 ≤ 696 :=
  smallPrimeAdvanceUpper 5218 25 692 4 0x11045c1030414100040c1000400103040010d040c107
    smallCountTo5218 (by decide +kernel)

theorem base_5243 : oddPrimeCount 5243 ≤ 696 := smallCountTo5243

set_option maxRecDepth 10000 in
private theorem smallCountTo5256 : oddPrimeCount 5256 ≤ 696 :=
  smallPrimeAdvanceUpper 5243 13 696 0 0x20a081823a09d820608282
    smallCountTo5243 (by decide +kernel)

theorem base_5256 : oddPrimeCount 5256 ≤ 696 := smallCountTo5256

set_option maxRecDepth 10000 in
private theorem smallCountTo5318 : oddPrimeCount 5318 ≤ 703 :=
  smallPrimeAdvanceUpper 5256 62 696 7 0x382060800226081822e0858206080020a08182000800206082822208182160a18206080020e08182000828206080025e081820a08682
    smallCountTo5256 (by decide +kernel)

theorem base_5318 : oddPrimeCount 5318 ≤ 703 := smallCountTo5318

set_option maxRecDepth 10000 in
private theorem smallCountTo5364 : oddPrimeCount 5364 ≤ 707 :=
  smallPrimeAdvanceUpper 5318 46 703 4 0x182220800206083829208182000828206089820e081820a0800206080026a081821608b820608f82
    smallCountTo5318 (by decide +kernel)

theorem base_5364 : oddPrimeCount 5364 ≤ 707 := smallCountTo5364

set_option maxRecDepth 10000 in
private theorem smallCountTo5366 : oddPrimeCount 5366 ≤ 707 :=
  smallPrimeAdvanceUpper 5364 2 707 0 0x282
    smallCountTo5364 (by decide +kernel)

theorem base_5366 : oddPrimeCount 5366 ≤ 707 := smallCountTo5366

set_option maxRecDepth 10000 in
private theorem smallCountTo5370 : oddPrimeCount 5370 ≤ 707 :=
  smallPrimeAdvanceUpper 5366 4 707 0 0x608382
    smallCountTo5366 (by decide +kernel)

theorem base_5370 : oddPrimeCount 5370 ≤ 707 := smallCountTo5370

set_option maxRecDepth 10000 in
private theorem smallCountTo5385 : oddPrimeCount 5385 ≤ 708 :=
  smallPrimeAdvanceUpper 5370 15 707 1 0xa41030414113040c100041c103
    smallCountTo5370 (by decide +kernel)

theorem base_5385 : oddPrimeCount 5385 ≤ 708 := smallCountTo5385

set_option maxRecDepth 10000 in
private theorem smallCountTo5449 : oddPrimeCount 5449 ≤ 720 :=
  smallPrimeAdvanceUpper 5385 64 708 12 0x400111040c1000414103040010b040c1050400103041c100040c1000400103042c105040c13d04001030414100040c10004001030434100
    smallCountTo5385 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5459 : oddPrimeCount 5459 ≤ 720 :=
  smallPrimeAdvanceUpper 5449 10 720 0 0x103041c105040c135
    smallCountTo5449 (by decide +kernel)

theorem base_5459 : oddPrimeCount 5459 ≤ 720 := smallCountTo5459

set_option maxRecDepth 10000 in
private theorem smallCountTo5469 : oddPrimeCount 5469 ≤ 720 :=
  smallPrimeAdvanceUpper 5459 10 720 0 0x12b040c105041c103
    smallCountTo5459 (by decide +kernel)

theorem base_5469 : oddPrimeCount 5469 ≤ 720 := smallCountTo5469

set_option maxRecDepth 10000 in
private theorem smallCountTo5474 : oddPrimeCount 5474 ≤ 721 :=
  smallPrimeAdvanceUpper 5469 5 720 1 0x20008682
    smallCountTo5469 (by decide +kernel)

theorem base_5474 : oddPrimeCount 5474 ≤ 721 := smallCountTo5474

set_option maxRecDepth 10000 in
private theorem smallCountTo5489 : oddPrimeCount 5489 ≤ 724 :=
  smallPrimeAdvanceUpper 5474 15 721 3 0xc10004001030400105040c10b
    smallCountTo5474 (by decide +kernel)

theorem base_5489 : oddPrimeCount 5489 ≤ 724 := smallCountTo5489

set_option maxRecDepth 10000 in
private theorem smallCountTo5496 : oddPrimeCount 5496 ≤ 724 :=
  smallPrimeAdvanceUpper 5489 7 724 0 0x88820608282
    smallCountTo5489 (by decide +kernel)

theorem base_5496 : oddPrimeCount 5496 ≤ 724 := smallCountTo5496

set_option maxRecDepth 10000 in
private theorem smallCountTo5502 : oddPrimeCount 5502 ≤ 725 :=
  smallPrimeAdvanceUpper 5496 6 724 1 0xb820608002
    smallCountTo5496 (by decide +kernel)

theorem base_5502 : oddPrimeCount 5502 ≤ 725 := smallCountTo5502

set_option maxRecDepth 10000 in
private theorem smallCountTo5504 : oddPrimeCount 5504 ≤ 726 :=
  smallPrimeAdvanceUpper 5502 2 725 1 0x2
    smallCountTo5502 (by decide +kernel)

theorem base_5504 : oddPrimeCount 5504 ≤ 726 := smallCountTo5504

set_option maxRecDepth 10000 in
private theorem smallCountTo5541 : oddPrimeCount 5541 ≤ 731 :=
  smallPrimeAdvanceUpper 5504 37 726 5 0x30400107040c12504141030400100040c1050400103040010b040c1070474103
    smallCountTo5504 (by decide +kernel)

theorem base_5541 : oddPrimeCount 5541 ≤ 731 := smallCountTo5541

set_option maxRecDepth 10000 in
private theorem smallCountTo5558 : oddPrimeCount 5558 ≤ 732 :=
  smallPrimeAdvanceUpper 5541 17 731 1 0x22e082820608f820e081820a08002
    smallCountTo5541 (by decide +kernel)

theorem base_5558 : oddPrimeCount 5558 ≤ 732 := smallCountTo5558

set_option maxRecDepth 10000 in
private theorem smallCountTo5561 : oddPrimeCount 5561 ≤ 732 :=
  smallPrimeAdvanceUpper 5558 3 732 0 0xc143
    smallCountTo5558 (by decide +kernel)

theorem base_5561 : oddPrimeCount 5561 ≤ 732 := smallCountTo5561

set_option maxRecDepth 10000 in
private theorem smallCountTo5605 : oddPrimeCount 5605 ≤ 737 :=
  smallPrimeAdvanceUpper 5561 44 732 5 0x400103044c100040c1000414103041c100040c10504941030400107040c11d042c1030434105
    smallCountTo5561 (by decide +kernel)

theorem base_5605 : oddPrimeCount 5605 ≤ 737 := smallCountTo5605

set_option maxRecDepth 10000 in
private theorem smallCountTo5617 : oddPrimeCount 5617 ≤ 737 :=
  smallPrimeAdvanceUpper 5605 12 737 0 0x40c147047c1030414129
    smallCountTo5605 (by decide +kernel)

theorem base_5617 : oddPrimeCount 5617 ≤ 737 := smallCountTo5617

set_option maxRecDepth 10000 in
private theorem smallCountTo5621 : oddPrimeCount 5621 ≤ 737 :=
  smallPrimeAdvanceUpper 5617 4 737 0 0x40c107
    smallCountTo5617 (by decide +kernel)

theorem base_5621 : oddPrimeCount 5621 ≤ 737 := smallCountTo5621

set_option maxRecDepth 10000 in
private theorem smallCountTo5646 : oddPrimeCount 5646 ≤ 740 :=
  smallPrimeAdvanceUpper 5621 25 737 3 0x20008182220868206095820a0818200080020608282
    smallCountTo5621 (by decide +kernel)

theorem base_5646 : oddPrimeCount 5646 ≤ 740 := smallCountTo5646

set_option maxRecDepth 10000 in
private theorem smallCountTo5659 : oddPrimeCount 5659 ≤ 745 :=
  smallPrimeAdvanceUpper 5646 13 740 5 0x40c10004001030400100
    smallCountTo5646 (by decide +kernel)

theorem base_5659 : oddPrimeCount 5659 ≤ 745 := smallCountTo5659

set_option maxRecDepth 10000 in
private theorem smallCountTo5689 : oddPrimeCount 5689 ≤ 748 :=
  smallPrimeAdvanceUpper 5659 30 745 3 0x103041c105040c10004d41030414107040c10d0400103042c100
    smallCountTo5659 (by decide +kernel)

theorem base_5689 : oddPrimeCount 5689 ≤ 748 := smallCountTo5689

set_option maxRecDepth 10000 in
private theorem smallCountTo5738 : oddPrimeCount 5738 ≤ 753 :=
  smallPrimeAdvanceUpper 5689 49 748 5 0x206080020a08182520800206082821a081820008e8206080020e081827608282060888216081820a08002
    smallCountTo5689 (by decide +kernel)

theorem base_5738 : oddPrimeCount 5738 ≤ 753 := smallCountTo5738

set_option maxRecDepth 10000 in
private theorem smallCountTo5743 : oddPrimeCount 5743 ≤ 755 :=
  smallPrimeAdvanceUpper 5738 5 753 2 0x30400100
    smallCountTo5738 (by decide +kernel)

theorem base_5743 : oddPrimeCount 5743 ≤ 755 := smallCountTo5743

set_option maxRecDepth 10000 in
private theorem smallCountTo5748 : oddPrimeCount 5748 ≤ 755 :=
  smallPrimeAdvanceUpper 5743 5 755 0 0x20608382
    smallCountTo5743 (by decide +kernel)

theorem base_5748 : oddPrimeCount 5748 ≤ 755 := smallCountTo5748

set_option maxRecDepth 10000 in
private theorem smallCountTo5754 : oddPrimeCount 5754 ≤ 756 :=
  smallPrimeAdvanceUpper 5748 6 755 1 0x20608582
    smallCountTo5748 (by decide +kernel)

theorem base_5754 : oddPrimeCount 5754 ≤ 756 := smallCountTo5754

set_option maxRecDepth 10000 in
private theorem smallCountTo5760 : oddPrimeCount 5760 ≤ 756 :=
  smallPrimeAdvanceUpper 5754 6 756 0 0x2820608682
    smallCountTo5754 (by decide +kernel)

theorem base_5760 : oddPrimeCount 5760 ≤ 756 := smallCountTo5760

set_option maxRecDepth 10000 in
private theorem smallCountTo5762 : oddPrimeCount 5762 ≤ 756 :=
  smallPrimeAdvanceUpper 5760 2 756 0 0x382
    smallCountTo5760 (by decide +kernel)

theorem base_5762 : oddPrimeCount 5762 ≤ 756 := smallCountTo5762

set_option maxRecDepth 10000 in
private theorem smallCountTo5765 : oddPrimeCount 5765 ≤ 756 :=
  smallPrimeAdvanceUpper 5762 3 756 0 0xc105
    smallCountTo5762 (by decide +kernel)

theorem base_5765 : oddPrimeCount 5765 ≤ 756 := smallCountTo5765

set_option maxRecDepth 10000 in
private theorem smallCountTo5771 : oddPrimeCount 5771 ≤ 756 :=
  smallPrimeAdvanceUpper 5765 6 756 0 0x149040c11d
    smallCountTo5765 (by decide +kernel)

theorem base_5771 : oddPrimeCount 5771 ≤ 756 := smallCountTo5771

set_option maxRecDepth 10000 in
private theorem smallCountTo5835 : oddPrimeCount 5835 ≤ 764 :=
  smallPrimeAdvanceUpper 5771 64 756 8 0x45c10304d4100040c1000414103041c100040c105042c1030400107040c10004941030400105040c10b04001030414100040c107044c103
    smallCountTo5771 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5899 : oddPrimeCount 5899 ≤ 775 :=
  smallPrimeAdvanceUpper 5835 64 764 11 0x434100040c10004141030400100040c1050400103040010b040c1000400103041c105040c10004001030414107040c12b051c1030400111
    smallCountTo5835 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo5907 : oddPrimeCount 5907 ≤ 776 :=
  smallPrimeAdvanceUpper 5899 8 775 1 0x40c1000414103
    smallCountTo5899 (by decide +kernel)

theorem base_5907 : oddPrimeCount 5907 ≤ 776 := smallCountTo5907

set_option maxRecDepth 10000 in
private theorem smallCountTo5934 : oddPrimeCount 5934 ≤ 778 :=
  smallPrimeAdvanceUpper 5907 27 776 2 0x89822e081820a09e820608f82000818200083820608882
    smallCountTo5907 (by decide +kernel)

theorem base_5934 : oddPrimeCount 5934 ≤ 778 := smallCountTo5934

set_option maxRecDepth 10000 in
private theorem smallCountTo5936 : oddPrimeCount 5936 ≤ 778 :=
  smallPrimeAdvanceUpper 5934 2 778 0 0x282
    smallCountTo5934 (by decide +kernel)

theorem base_5936 : oddPrimeCount 5936 ≤ 778 := smallCountTo5936

set_option maxRecDepth 10000 in
private theorem smallCountTo5940 : oddPrimeCount 5940 ≤ 779 :=
  smallPrimeAdvanceUpper 5936 4 778 1 0x608002
    smallCountTo5936 (by decide +kernel)

theorem base_5940 : oddPrimeCount 5940 ≤ 779 := smallCountTo5940

set_option maxRecDepth 10000 in
private theorem smallCountTo5951 : oddPrimeCount 5951 ≤ 779 :=
  smallPrimeAdvanceUpper 5940 11 779 0 0x341030414113040c10b
    smallCountTo5940 (by decide +kernel)

theorem base_5951 : oddPrimeCount 5951 ≤ 779 := smallCountTo5951

set_option maxRecDepth 10000 in
private theorem smallCountTo5973 : oddPrimeCount 5973 ≤ 780 :=
  smallPrimeAdvanceUpper 5951 22 779 1 0x100040c10704ec103050c105040c12f041c103
    smallCountTo5951 (by decide +kernel)

theorem base_5973 : oddPrimeCount 5973 ≤ 780 := smallCountTo5973

set_option maxRecDepth 10000 in
private theorem smallCountTo5980 : oddPrimeCount 5980 ≤ 780 :=
  smallPrimeAdvanceUpper 5973 7 780 0 0x82825608182
    smallCountTo5973 (by decide +kernel)

theorem base_5980 : oddPrimeCount 5980 ≤ 780 := smallCountTo5980

set_option maxRecDepth 10000 in
private theorem smallCountTo6020 : oddPrimeCount 6020 ≤ 784 :=
  smallPrimeAdvanceUpper 5980 40 780 4 0x8f8206080026a081821a08282060838222081820a0800206080020e081821608682
    smallCountTo5980 (by decide +kernel)

theorem base_6020 : oddPrimeCount 6020 ≤ 784 := smallCountTo6020

set_option maxRecDepth 10000 in
private theorem smallCountTo6025 : oddPrimeCount 6025 ≤ 784 :=
  smallPrimeAdvanceUpper 6020 5 784 0 0x3044c105
    smallCountTo6020 (by decide +kernel)

theorem base_6025 : oddPrimeCount 6025 ≤ 784 := smallCountTo6025

set_option maxRecDepth 10000 in
private theorem smallCountTo6026 : oddPrimeCount 6026 ≤ 784 :=
  smallPrimeAdvanceUpper 6025 1 784 0 0x2
    smallCountTo6025 (by decide +kernel)

theorem base_6026 : oddPrimeCount 6026 ≤ 784 := smallCountTo6026

set_option maxRecDepth 10000 in
private theorem smallCountTo6035 : oddPrimeCount 6035 ≤ 785 :=
  smallPrimeAdvanceUpper 6026 9 784 1 0x30400125040c105
    smallCountTo6026 (by decide +kernel)

theorem base_6035 : oddPrimeCount 6035 ≤ 785 := smallCountTo6035

set_option maxRecDepth 10000 in
private theorem smallCountTo6059 : oddPrimeCount 6059 ≤ 789 :=
  smallPrimeAdvanceUpper 6035 24 785 4 0x400103041c100040c100045c1030400105040c149
    smallCountTo6035 (by decide +kernel)

theorem base_6059 : oddPrimeCount 6059 ≤ 789 := smallCountTo6059

set_option maxRecDepth 10000 in
private theorem smallCountTo6123 : oddPrimeCount 6123 ≤ 797 :=
  smallPrimeAdvanceUpper 6059 64 789 8 0x42c1030414100040c10d040010304ec100040c10704141030400100040c105041c1030400111040c11f04a41030400105040c11d0400103
    smallCountTo6059 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6146 : oddPrimeCount 6146 ≤ 800 :=
  smallPrimeAdvanceUpper 6123 23 797 3 0x82821608182000800206088820e081820008282
    smallCountTo6123 (by decide +kernel)

theorem base_6146 : oddPrimeCount 6146 ≤ 800 := smallCountTo6146

set_option maxRecDepth 10000 in
private theorem smallCountTo6147 : oddPrimeCount 6147 ≤ 800 :=
  smallPrimeAdvanceUpper 6146 1 800 0 0x3
    smallCountTo6146 (by decide +kernel)

theorem base_6147 : oddPrimeCount 6147 ≤ 800 := smallCountTo6147

set_option maxRecDepth 10000 in
private theorem smallCountTo6150 : oddPrimeCount 6150 ≤ 800 :=
  smallPrimeAdvanceUpper 6147 3 800 0 0x8582
    smallCountTo6147 (by decide +kernel)

theorem base_6150 : oddPrimeCount 6150 ≤ 800 := smallCountTo6150

set_option maxRecDepth 10000 in
private theorem smallCountTo6199 : oddPrimeCount 6199 ≤ 805 :=
  smallPrimeAdvanceUpper 6150 49 800 5 0x40c10504bc10304f4100040c107047c1030400105040c125041c1030414117040c129042c1030400100
    smallCountTo6150 (by decide +kernel)

theorem base_6199 : oddPrimeCount 6199 ≤ 805 := smallCountTo6199

set_option maxRecDepth 10000 in
private theorem smallCountTo6208 : oddPrimeCount 6208 ≤ 806 :=
  smallPrimeAdvanceUpper 6199 9 805 1 0x206080020a08182
    smallCountTo6199 (by decide +kernel)

theorem base_6208 : oddPrimeCount 6208 ≤ 806 := smallCountTo6208

set_option maxRecDepth 10000 in
private theorem smallCountTo6242 : oddPrimeCount 6242 ≤ 810 :=
  smallPrimeAdvanceUpper 6208 34 806 4 0x38200081820a0800206080020e081821a080020608b820a08182220a782
    smallCountTo6208 (by decide +kernel)

theorem base_6242 : oddPrimeCount 6242 ≤ 810 := smallCountTo6242

set_option maxRecDepth 10000 in
private theorem smallCountTo6259 : oddPrimeCount 6259 ≤ 812 :=
  smallPrimeAdvanceUpper 6242 17 810 2 0x30414100040c1070434103040010b
    smallCountTo6242 (by decide +kernel)

theorem base_6259 : oddPrimeCount 6259 ≤ 812 := smallCountTo6259

set_option maxRecDepth 10000 in
private theorem smallCountTo6270 : oddPrimeCount 6270 ≤ 814 :=
  smallPrimeAdvanceUpper 6259 11 812 2 0x818200082820608002
    smallCountTo6259 (by decide +kernel)

theorem base_6270 : oddPrimeCount 6270 ≤ 814 := smallCountTo6270

set_option maxRecDepth 10000 in
private theorem smallCountTo6271 : oddPrimeCount 6271 ≤ 815 :=
  smallPrimeAdvanceUpper 6270 1 814 1 0x0
    smallCountTo6270 (by decide +kernel)

theorem base_6271 : oddPrimeCount 6271 ≤ 815 := smallCountTo6271

set_option maxRecDepth 10000 in
private theorem smallCountTo6315 : oddPrimeCount 6315 ≤ 820 :=
  smallPrimeAdvanceUpper 6271 44 815 5 0x40c1050400103042c13d040c100044c103041c105040c10004001030414107040c10004ec103
    smallCountTo6271 (by decide +kernel)

theorem base_6315 : oddPrimeCount 6315 ≤ 820 := smallCountTo6315

set_option maxRecDepth 10000 in
private theorem smallCountTo6316 : oddPrimeCount 6316 ≤ 820 :=
  smallPrimeAdvanceUpper 6315 1 820 0 0x2
    smallCountTo6315 (by decide +kernel)

theorem base_6316 : oddPrimeCount 6316 ≤ 820 := smallCountTo6316

set_option maxRecDepth 10000 in
private theorem smallCountTo6322 : oddPrimeCount 6322 ≤ 821 :=
  smallPrimeAdvanceUpper 6316 6 820 1 0x28e08182
    smallCountTo6316 (by decide +kernel)

theorem base_6322 : oddPrimeCount 6322 ≤ 821 := smallCountTo6322

set_option maxRecDepth 10000 in
private theorem smallCountTo6336 : oddPrimeCount 6336 ≤ 823 :=
  smallPrimeAdvanceUpper 6322 14 821 2 0x20a0818200086820608282
    smallCountTo6322 (by decide +kernel)

theorem base_6336 : oddPrimeCount 6336 ≤ 823 := smallCountTo6336

set_option maxRecDepth 10000 in
private theorem smallCountTo6345 : oddPrimeCount 6345 ≤ 825 :=
  smallPrimeAdvanceUpper 6336 9 823 2 0x40c1110400103
    smallCountTo6336 (by decide +kernel)

theorem base_6345 : oddPrimeCount 6345 ≤ 825 := smallCountTo6345

set_option maxRecDepth 10000 in
private theorem smallCountTo6351 : oddPrimeCount 6351 ≤ 825 :=
  smallPrimeAdvanceUpper 6345 6 825 0 0x10b041c103
    smallCountTo6345 (by decide +kernel)

theorem base_6351 : oddPrimeCount 6351 ≤ 825 := smallCountTo6351

set_option maxRecDepth 10000 in
private theorem smallCountTo6359 : oddPrimeCount 6359 ≤ 827 :=
  smallPrimeAdvanceUpper 6351 8 825 2 0x400105040c100
    smallCountTo6351 (by decide +kernel)

theorem base_6359 : oddPrimeCount 6359 ≤ 827 := smallCountTo6359

set_option maxRecDepth 10000 in
private theorem smallCountTo6396 : oddPrimeCount 6396 ≤ 832 :=
  smallPrimeAdvanceUpper 6359 37 827 5 0x200081820a080020608b8200081820e0800206086820a0818200083820608282
    smallCountTo6359 (by decide +kernel)

theorem base_6396 : oddPrimeCount 6396 ≤ 832 := smallCountTo6396

set_option maxRecDepth 10000 in
private theorem smallCountTo6398 : oddPrimeCount 6398 ≤ 833 :=
  smallPrimeAdvanceUpper 6396 2 832 1 0x2
    smallCountTo6396 (by decide +kernel)

theorem base_6398 : oddPrimeCount 6398 ≤ 833 := smallCountTo6398

set_option maxRecDepth 10000 in
private theorem smallCountTo6406 : oddPrimeCount 6406 ≤ 833 :=
  smallPrimeAdvanceUpper 6398 8 833 0 0x6092822608182
    smallCountTo6398 (by decide +kernel)

theorem base_6406 : oddPrimeCount 6406 ≤ 833 := smallCountTo6406

set_option maxRecDepth 10000 in
private theorem smallCountTo6413 : oddPrimeCount 6413 ≤ 833 :=
  smallPrimeAdvanceUpper 6406 7 833 0 0xac10d040c10b
    smallCountTo6406 (by decide +kernel)

theorem base_6413 : oddPrimeCount 6413 ≤ 833 := smallCountTo6413

set_option maxRecDepth 10000 in
private theorem smallCountTo6432 : oddPrimeCount 6432 ≤ 835 :=
  smallPrimeAdvanceUpper 6413 19 833 2 0x8282060838200081820a080020609d82
    smallCountTo6413 (by decide +kernel)

theorem base_6432 : oddPrimeCount 6432 ≤ 835 := smallCountTo6432

set_option maxRecDepth 10000 in
private theorem smallCountTo6444 : oddPrimeCount 6444 ≤ 835 :=
  smallPrimeAdvanceUpper 6432 12 835 0 0xe0818252097820608882
    smallCountTo6432 (by decide +kernel)

theorem base_6444 : oddPrimeCount 6444 ≤ 835 := smallCountTo6444

set_option maxRecDepth 10000 in
private theorem smallCountTo6508 : oddPrimeCount 6508 ≤ 841 :=
  smallPrimeAdvanceUpper 6444 64 835 6 0xa081820008002060828216081820e08b820608e8200081820008282060858200081820a0868206080025608182920a18206083820a08182
    smallCountTo6444 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6526 : oddPrimeCount 6526 ≤ 842 :=
  smallPrimeAdvanceUpper 6508 18 841 1 0xb8222081820a0838206080021608182
    smallCountTo6508 (by decide +kernel)

theorem base_6526 : oddPrimeCount 6526 ≤ 842 := smallCountTo6526

set_option maxRecDepth 10000 in
private theorem smallCountTo6527 : oddPrimeCount 6527 ≤ 842 :=
  smallPrimeAdvanceUpper 6526 1 842 0 0x3d
    smallCountTo6526 (by decide +kernel)

theorem base_6527 : oddPrimeCount 6527 ≤ 842 := smallCountTo6527

set_option maxRecDepth 10000 in
private theorem smallCountTo6566 : oddPrimeCount 6566 ≤ 847 :=
  smallPrimeAdvanceUpper 6527 39 842 5 0x800206097820a081821a08f82060828200081820008002060a7820e081820008282
    smallCountTo6527 (by decide +kernel)

theorem base_6566 : oddPrimeCount 6566 ≤ 847 := smallCountTo6566

set_option maxRecDepth 10000 in
private theorem smallCountTo6584 : oddPrimeCount 6584 ≤ 851 :=
  smallPrimeAdvanceUpper 6566 18 847 4 0x1820008002060828200081820008e82
    smallCountTo6566 (by decide +kernel)

theorem base_6584 : oddPrimeCount 6584 ≤ 851 := smallCountTo6584

set_option maxRecDepth 10000 in
private theorem smallCountTo6628 : oddPrimeCount 6628 ≤ 854 :=
  smallPrimeAdvanceUpper 6584 44 851 3 0x6083821608182260828206080020e081820a08002060858222081821a0800206092820a08182
    smallCountTo6584 (by decide +kernel)

theorem base_6628 : oddPrimeCount 6628 ≤ 854 := smallCountTo6628

set_option maxRecDepth 10000 in
private theorem smallCountTo6634 : oddPrimeCount 6634 ≤ 854 :=
  smallPrimeAdvanceUpper 6628 6 854 0 0x3822608182
    smallCountTo6628 (by decide +kernel)

theorem base_6634 : oddPrimeCount 6634 ≤ 854 := smallCountTo6634

set_option maxRecDepth 10000 in
private theorem smallCountTo6659 : oddPrimeCount 6659 ≤ 857 :=
  smallPrimeAdvanceUpper 6634 25 854 3 0x504001030474107040c11104f41030400105040c100
    smallCountTo6634 (by decide +kernel)

theorem base_6659 : oddPrimeCount 6659 ≤ 857 := smallCountTo6659

set_option maxRecDepth 10000 in
private theorem smallCountTo6661 : oddPrimeCount 6661 ≤ 858 :=
  smallPrimeAdvanceUpper 6659 2 857 1 0x100
    smallCountTo6659 (by decide +kernel)

theorem base_6661 : oddPrimeCount 6661 ≤ 858 := smallCountTo6661

set_option maxRecDepth 10000 in
private theorem smallCountTo6669 : oddPrimeCount 6669 ≤ 858 :=
  smallPrimeAdvanceUpper 6661 8 858 0 0x40c10504ec103
    smallCountTo6661 (by decide +kernel)

theorem base_6669 : oddPrimeCount 6669 ≤ 858 := smallCountTo6669

set_option maxRecDepth 10000 in
private theorem smallCountTo6679 : oddPrimeCount 6679 ≤ 860 :=
  smallPrimeAdvanceUpper 6669 10 858 2 0x1070400103042c100
    smallCountTo6669 (by decide +kernel)

theorem base_6679 : oddPrimeCount 6679 ≤ 860 := smallCountTo6679

set_option maxRecDepth 10000 in
private theorem smallCountTo6694 : oddPrimeCount 6694 ≤ 862 :=
  smallPrimeAdvanceUpper 6679 15 860 2 0x8182520828206080020008182
    smallCountTo6679 (by decide +kernel)

theorem base_6694 : oddPrimeCount 6694 ≤ 862 := smallCountTo6694

set_option maxRecDepth 10000 in
private theorem smallCountTo6695 : oddPrimeCount 6695 ≤ 862 :=
  smallPrimeAdvanceUpper 6694 1 862 0 0x5
    smallCountTo6694 (by decide +kernel)

theorem base_6695 : oddPrimeCount 6695 ≤ 862 := smallCountTo6695

set_option maxRecDepth 10000 in
private theorem smallCountTo6759 : oddPrimeCount 6759 ≤ 868 :=
  smallPrimeAdvanceUpper 6695 64 862 6 0x4941030400100040c1130400103041c105040c100042c1030414107040c13504001030400117040c10b0414103044412b040c1050474103
    smallCountTo6695 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo6795 : oddPrimeCount 6795 ≤ 874 :=
  smallPrimeAdvanceUpper 6759 36 868 6 0x400100040c143041c1030434105040c1000400103041410b040c1000400103
    smallCountTo6759 (by decide +kernel)

theorem base_6795 : oddPrimeCount 6795 ≤ 874 := smallCountTo6795

set_option maxRecDepth 10000 in
private theorem smallCountTo6797 : oddPrimeCount 6797 ≤ 874 :=
  smallPrimeAdvanceUpper 6795 2 874 0 0x107
    smallCountTo6795 (by decide +kernel)

theorem base_6797 : oddPrimeCount 6797 ≤ 874 := smallCountTo6797

set_option maxRecDepth 10000 in
private theorem smallCountTo6827 : oddPrimeCount 6827 ≤ 877 :=
  smallPrimeAdvanceUpper 6797 30 874 3 0x10d040c1000414103042c107040c1050444103044c100040c100
    smallCountTo6797 (by decide +kernel)

theorem base_6827 : oddPrimeCount 6827 ≤ 877 := smallCountTo6827

set_option maxRecDepth 10000 in
private theorem smallCountTo6872 : oddPrimeCount 6872 ≤ 884 :=
  smallPrimeAdvanceUpper 6827 45 877 7 0x200081820008282060838200081820a0948206086820e08182000898206080020a081820008002
    smallCountTo6827 (by decide +kernel)

theorem base_6872 : oddPrimeCount 6872 ≤ 884 := smallCountTo6872

set_option maxRecDepth 10000 in
private theorem smallCountTo6909 : oddPrimeCount 6909 ≤ 887 :=
  smallPrimeAdvanceUpper 6872 37 884 3 0x3041410d040c1070400103051c153040c13d04141030400143040c1050400103
    smallCountTo6872 (by decide +kernel)

theorem base_6909 : oddPrimeCount 6909 ≤ 887 := smallCountTo6909

set_option maxRecDepth 10000 in
private theorem smallCountTo6917 : oddPrimeCount 6917 ≤ 889 :=
  smallPrimeAdvanceUpper 6909 8 887 2 0x40011f040c100
    smallCountTo6909 (by decide +kernel)

theorem base_6917 : oddPrimeCount 6917 ≤ 889 := smallCountTo6917

set_option maxRecDepth 10000 in
private theorem smallCountTo6924 : oddPrimeCount 6924 ≤ 889 :=
  smallPrimeAdvanceUpper 6917 7 889 0 0x85820608382
    smallCountTo6917 (by decide +kernel)

theorem base_6924 : oddPrimeCount 6924 ≤ 889 := smallCountTo6924

set_option maxRecDepth 10000 in
private theorem smallCountTo6929 : oddPrimeCount 6929 ≤ 889 :=
  smallPrimeAdvanceUpper 6924 5 889 0 0x5040c10d
    smallCountTo6924 (by decide +kernel)

theorem base_6929 : oddPrimeCount 6929 ≤ 889 := smallCountTo6929

set_option maxRecDepth 10000 in
private theorem smallCountTo6935 : oddPrimeCount 6935 ≤ 889 :=
  smallPrimeAdvanceUpper 6929 6 889 0 0x11d040c105
    smallCountTo6929 (by decide +kernel)

theorem base_6935 : oddPrimeCount 6935 ≤ 889 := smallCountTo6935

set_option maxRecDepth 10000 in
private theorem smallCountTo6937 : oddPrimeCount 6937 ≤ 889 :=
  smallPrimeAdvanceUpper 6935 2 889 0 0x107
    smallCountTo6935 (by decide +kernel)

theorem base_6937 : oddPrimeCount 6937 ≤ 889 := smallCountTo6937

set_option maxRecDepth 10000 in
private theorem smallCountTo6939 : oddPrimeCount 6939 ≤ 889 :=
  smallPrimeAdvanceUpper 6937 2 889 0 0x103
    smallCountTo6937 (by decide +kernel)

theorem base_6939 : oddPrimeCount 6939 ≤ 889 := smallCountTo6939

set_option maxRecDepth 10000 in
private theorem smallCountTo6955 : oddPrimeCount 6955 ≤ 891 :=
  smallPrimeAdvanceUpper 6939 16 889 2 0x42c135040c10004001030444105
    smallCountTo6939 (by decide +kernel)

theorem base_6955 : oddPrimeCount 6955 ≤ 891 := smallCountTo6955

set_option maxRecDepth 10000 in
private theorem smallCountTo6962 : oddPrimeCount 6962 ≤ 893 :=
  smallPrimeAdvanceUpper 6955 7 891 2 0x81820008002
    smallCountTo6955 (by decide +kernel)

theorem base_6962 : oddPrimeCount 6962 ≤ 893 := smallCountTo6962

set_option maxRecDepth 10000 in
private theorem smallCountTo7009 : oddPrimeCount 7009 ≤ 900 :=
  smallPrimeAdvanceUpper 6962 47 893 7 0xc10504001030400113040c100041c1030400105040c11d04001030414100040c10004bc103041c12b
    smallCountTo6962 (by decide +kernel)

theorem base_7009 : oddPrimeCount 7009 ≤ 900 := smallCountTo7009

set_option maxRecDepth 10000 in
private theorem smallCountTo7019 : oddPrimeCount 7019 ≤ 902 :=
  smallPrimeAdvanceUpper 7009 10 900 2 0x1030400105040c100
    smallCountTo7009 (by decide +kernel)

theorem base_7019 : oddPrimeCount 7019 ≤ 902 := smallCountTo7019

set_option maxRecDepth 10000 in
private theorem smallCountTo7047 : oddPrimeCount 7047 ≤ 905 :=
  smallPrimeAdvanceUpper 7019 28 902 3 0x41c1030414100040c14f0434103047c100040c1000414103
    smallCountTo7019 (by decide +kernel)

theorem base_7047 : oddPrimeCount 7047 ≤ 905 := smallCountTo7047

set_option maxRecDepth 10000 in
private theorem smallCountTo7077 : oddPrimeCount 7077 ≤ 907 :=
  smallPrimeAdvanceUpper 7047 30 905 2 0x107042c1030414100040c117041c1030494100040c10b0414103
    smallCountTo7047 (by decide +kernel)

theorem base_7077 : oddPrimeCount 7077 ≤ 907 := smallCountTo7077

set_option maxRecDepth 10000 in
private theorem smallCountTo7079 : oddPrimeCount 7079 ≤ 908 :=
  smallPrimeAdvanceUpper 7077 2 907 1 0x100
    smallCountTo7077 (by decide +kernel)

theorem base_7079 : oddPrimeCount 7079 ≤ 908 := smallCountTo7079

set_option maxRecDepth 10000 in
private theorem smallCountTo7143 : oddPrimeCount 7143 ≤ 913 :=
  smallPrimeAdvanceUpper 7079 64 908 5 0x5241030414113040c10704a410304bc11f040c1000414103040010d040c105042c1030400111040c1000400103041c105040c10b0494103
    smallCountTo7079 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7207 : oddPrimeCount 7207 ≤ 919 :=
  smallPrimeAdvanceUpper 7143 64 913 6 0x414107040c100045c1030444100040c10d0414103050c147040c105040010304ac10b040c100041c1030400105040c117044c1030414100
    smallCountTo7143 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7212 : oddPrimeCount 7212 ≤ 920 :=
  smallPrimeAdvanceUpper 7207 5 919 1 0x20608002
    smallCountTo7207 (by decide +kernel)

theorem base_7212 : oddPrimeCount 7212 ≤ 920 := smallCountTo7212

set_option maxRecDepth 10000 in
private theorem smallCountTo7219 : oddPrimeCount 7219 ≤ 922 :=
  smallPrimeAdvanceUpper 7212 7 920 2 0x103041c100
    smallCountTo7212 (by decide +kernel)

theorem base_7219 : oddPrimeCount 7219 ≤ 922 := smallCountTo7219

set_option maxRecDepth 10000 in
private theorem smallCountTo7222 : oddPrimeCount 7222 ≤ 922 :=
  smallPrimeAdvanceUpper 7219 3 922 0 0x8182
    smallCountTo7219 (by decide +kernel)

theorem base_7222 : oddPrimeCount 7222 ≤ 922 := smallCountTo7222

set_option maxRecDepth 10000 in
private theorem smallCountTo7225 : oddPrimeCount 7225 ≤ 922 :=
  smallPrimeAdvanceUpper 7222 3 922 0 0x7c105
    smallCountTo7222 (by decide +kernel)

theorem base_7225 : oddPrimeCount 7225 ≤ 922 := smallCountTo7225

set_option maxRecDepth 10000 in
private theorem smallCountTo7227 : oddPrimeCount 7227 ≤ 922 :=
  smallPrimeAdvanceUpper 7225 2 922 0 0x103
    smallCountTo7225 (by decide +kernel)

theorem base_7227 : oddPrimeCount 7227 ≤ 922 := smallCountTo7227

set_option maxRecDepth 10000 in
private theorem smallCountTo7228 : oddPrimeCount 7228 ≤ 922 :=
  smallPrimeAdvanceUpper 7227 1 922 0 0x2
    smallCountTo7227 (by decide +kernel)

theorem base_7228 : oddPrimeCount 7228 ≤ 922 := smallCountTo7228

set_option maxRecDepth 10000 in
private theorem smallCountTo7270 : oddPrimeCount 7270 ≤ 927 :=
  smallPrimeAdvanceUpper 7228 42 922 5 0x20e081820a0800206086820008182000858206080020a081820e09a8206082821a08182
    smallCountTo7228 (by decide +kernel)

theorem base_7270 : oddPrimeCount 7270 ≤ 927 := smallCountTo7270

set_option maxRecDepth 10000 in
private theorem smallCountTo7294 : oddPrimeCount 7294 ≤ 928 :=
  smallPrimeAdvanceUpper 7270 24 927 1 0x160838206089823a08182000828206092822e08182
    smallCountTo7270 (by decide +kernel)

theorem base_7294 : oddPrimeCount 7294 ≤ 928 := smallCountTo7294

set_option maxRecDepth 10000 in
private theorem smallCountTo7298 : oddPrimeCount 7298 ≤ 929 :=
  smallPrimeAdvanceUpper 7294 4 928 1 0xa08002
    smallCountTo7294 (by decide +kernel)

theorem base_7298 : oddPrimeCount 7298 ≤ 929 := smallCountTo7298

set_option maxRecDepth 10000 in
private theorem smallCountTo7306 : oddPrimeCount 7306 ≤ 929 :=
  smallPrimeAdvanceUpper 7298 8 929 0 0x6083828608182
    smallCountTo7298 (by decide +kernel)

theorem base_7306 : oddPrimeCount 7306 ≤ 929 := smallCountTo7306

set_option maxRecDepth 10000 in
private theorem smallCountTo7370 : oddPrimeCount 7370 ≤ 937 :=
  smallPrimeAdvanceUpper 7306 64 929 8 0x8002060a3820a081821a08002060828222081820008002060858252081820e08282060800200081820a0838206088824a081826a08002
    smallCountTo7306 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7371 : oddPrimeCount 7371 ≤ 937 :=
  smallPrimeAdvanceUpper 7370 1 937 0 0x3
    smallCountTo7370 (by decide +kernel)

theorem base_7371 : oddPrimeCount 7371 ≤ 937 := smallCountTo7371

set_option maxRecDepth 10000 in
private theorem smallCountTo7374 : oddPrimeCount 7374 ≤ 937 :=
  smallPrimeAdvanceUpper 7371 3 937 0 0xa482
    smallCountTo7371 (by decide +kernel)

theorem base_7374 : oddPrimeCount 7374 ≤ 937 := smallCountTo7374

set_option maxRecDepth 10000 in
private theorem smallCountTo7410 : oddPrimeCount 7410 ≤ 938 :=
  smallPrimeAdvanceUpper 7374 36 937 1 0xa081825e085820608282a608182260800206086820e0818216082820608f82
    smallCountTo7374 (by decide +kernel)

theorem base_7410 : oddPrimeCount 7410 ≤ 938 := smallCountTo7410

set_option maxRecDepth 10000 in
private theorem smallCountTo7419 : oddPrimeCount 7419 ≤ 940 :=
  smallPrimeAdvanceUpper 7410 9 938 2 0x40c1050400103
    smallCountTo7410 (by decide +kernel)

theorem base_7419 : oddPrimeCount 7419 ≤ 940 := smallCountTo7419

set_option maxRecDepth 10000 in
private theorem smallCountTo7448 : oddPrimeCount 7448 ≤ 941 :=
  smallPrimeAdvanceUpper 7419 29 940 1 0x2520868206083822208182000828206095820e081820a08582
    smallCountTo7419 (by decide +kernel)

theorem base_7448 : oddPrimeCount 7448 ≤ 941 := smallCountTo7448

set_option maxRecDepth 10000 in
private theorem smallCountTo7469 : oddPrimeCount 7469 ≤ 944 :=
  smallPrimeAdvanceUpper 7448 21 941 3 0x3040011d040c10004001030444105040c107
    smallCountTo7448 (by decide +kernel)

theorem base_7469 : oddPrimeCount 7469 ≤ 944 := smallCountTo7469

set_option maxRecDepth 10000 in
private theorem smallCountTo7477 : oddPrimeCount 7477 ≤ 945 :=
  smallPrimeAdvanceUpper 7469 8 944 1 0x47c1030414100
    smallCountTo7469 (by decide +kernel)

theorem base_7477 : oddPrimeCount 7477 ≤ 945 := smallCountTo7477

set_option maxRecDepth 10000 in
private theorem smallCountTo7505 : oddPrimeCount 7505 ≤ 949 :=
  smallPrimeAdvanceUpper 7477 28 945 4 0x40c100041c1030400100040c13b0414103040010d040c105
    smallCountTo7477 (by decide +kernel)

theorem base_7505 : oddPrimeCount 7505 ≤ 949 := smallCountTo7505

set_option maxRecDepth 10000 in
private theorem smallCountTo7523 : oddPrimeCount 7523 ≤ 952 :=
  smallPrimeAdvanceUpper 7505 18 949 3 0x100040c107042c1030400149040c100
    smallCountTo7505 (by decide +kernel)

theorem base_7523 : oddPrimeCount 7523 ≤ 952 := smallCountTo7523

set_option maxRecDepth 10000 in
private theorem smallCountTo7524 : oddPrimeCount 7524 ≤ 952 :=
  smallPrimeAdvanceUpper 7523 1 952 0 0x2
    smallCountTo7523 (by decide +kernel)

theorem base_7524 : oddPrimeCount 7524 ≤ 952 := smallCountTo7524

set_option maxRecDepth 10000 in
private theorem smallCountTo7527 : oddPrimeCount 7527 ≤ 952 :=
  smallPrimeAdvanceUpper 7524 3 952 0 0x14103
    smallCountTo7524 (by decide +kernel)

theorem base_7527 : oddPrimeCount 7527 ≤ 952 := smallCountTo7527

set_option maxRecDepth 10000 in
private theorem smallCountTo7578 : oddPrimeCount 7578 ≤ 961 :=
  smallPrimeAdvanceUpper 7527 51 952 9 0x800222081820a0800206080022608182000800206083820a08182000800206082820e0818286080020608002
    smallCountTo7527 (by decide +kernel)

theorem base_7578 : oddPrimeCount 7578 ≤ 961 := smallCountTo7578

set_option maxRecDepth 10000 in
private theorem smallCountTo7642 : oddPrimeCount 7642 ≤ 968 :=
  smallPrimeAdvanceUpper 7578 64 961 7 0x16081820008282060800200081820a0a3820608582000818200083820608b820a08182260800206082823a081821a0888206083820008182
    smallCountTo7578 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7655 : oddPrimeCount 7655 ≤ 970 :=
  smallPrimeAdvanceUpper 7642 13 968 2 0x4141030400107040c105
    smallCountTo7642 (by decide +kernel)

theorem base_7655 : oddPrimeCount 7655 ≤ 970 := smallCountTo7655

set_option maxRecDepth 10000 in
private theorem smallCountTo7659 : oddPrimeCount 7659 ≤ 970 :=
  smallPrimeAdvanceUpper 7655 4 970 0 0x434103
    smallCountTo7655 (by decide +kernel)

theorem base_7659 : oddPrimeCount 7659 ≤ 970 := smallCountTo7659

set_option maxRecDepth 10000 in
private theorem smallCountTo7667 : oddPrimeCount 7667 ≤ 970 :=
  smallPrimeAdvanceUpper 7659 8 970 0 0x4bc14f040c10b
    smallCountTo7659 (by decide +kernel)

theorem base_7667 : oddPrimeCount 7667 ≤ 970 := smallCountTo7667

set_option maxRecDepth 10000 in
private theorem smallCountTo7679 : oddPrimeCount 7679 ≤ 972 :=
  smallPrimeAdvanceUpper 7667 12 970 2 0x4001030400105040c107
    smallCountTo7667 (by decide +kernel)

theorem base_7679 : oddPrimeCount 7679 ≤ 972 := smallCountTo7679

set_option maxRecDepth 10000 in
private theorem smallCountTo7680 : oddPrimeCount 7680 ≤ 972 :=
  smallPrimeAdvanceUpper 7679 1 972 0 0x2
    smallCountTo7679 (by decide +kernel)

theorem base_7680 : oddPrimeCount 7680 ≤ 972 := smallCountTo7680

set_option maxRecDepth 10000 in
private theorem smallCountTo7683 : oddPrimeCount 7683 ≤ 973 :=
  smallPrimeAdvanceUpper 7680 3 972 1 0x103
    smallCountTo7680 (by decide +kernel)

theorem base_7683 : oddPrimeCount 7683 ≤ 973 := smallCountTo7683

set_option maxRecDepth 10000 in
private theorem smallCountTo7747 : oddPrimeCount 7747 ≤ 981 :=
  smallPrimeAdvanceUpper 7683 64 973 8 0x414100040c100041c10304ac100040c1000414103043410b040c1050400103041c100040c10004ec103042c105040c1470400103041413d
    smallCountTo7683 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo7781 : oddPrimeCount 7781 ≤ 984 :=
  smallPrimeAdvanceUpper 7747 34 981 3 0x103045c100040c1000400103041c105040c111044c1030414107040c11f
    smallCountTo7747 (by decide +kernel)

theorem base_7781 : oddPrimeCount 7781 ≤ 984 := smallCountTo7781

set_option maxRecDepth 10000 in
private theorem smallCountTo7810 : oddPrimeCount 7810 ≤ 986 :=
  smallPrimeAdvanceUpper 7781 29 984 2 0x256081821a0800206080020a081821608e8206082824a08182
    smallCountTo7781 (by decide +kernel)

theorem base_7810 : oddPrimeCount 7810 ≤ 986 := smallCountTo7810

set_option maxRecDepth 10000 in
private theorem smallCountTo7813 : oddPrimeCount 7813 ≤ 986 :=
  smallPrimeAdvanceUpper 7810 3 986 0 0x12410d
    smallCountTo7810 (by decide +kernel)

theorem base_7813 : oddPrimeCount 7813 ≤ 986 := smallCountTo7813

set_option maxRecDepth 10000 in
private theorem smallCountTo7828 : oddPrimeCount 7828 ≤ 988 :=
  smallPrimeAdvanceUpper 7813 15 986 2 0x8182000838206080020a08182
    smallCountTo7813 (by decide +kernel)

theorem base_7828 : oddPrimeCount 7828 ≤ 988 := smallCountTo7828

set_option maxRecDepth 10000 in
private theorem smallCountTo7829 : oddPrimeCount 7829 ≤ 989 :=
  smallPrimeAdvanceUpper 7828 1 988 1 0x0
    smallCountTo7828 (by decide +kernel)

theorem base_7829 : oddPrimeCount 7829 ≤ 989 := smallCountTo7829

set_option maxRecDepth 10000 in
private theorem smallCountTo7840 : oddPrimeCount 7840 ≤ 989 :=
  smallPrimeAdvanceUpper 7829 11 989 0 0x948206082822208182
    smallCountTo7829 (by decide +kernel)

theorem base_7840 : oddPrimeCount 7840 ≤ 989 := smallCountTo7840

set_option maxRecDepth 10000 in
private theorem smallCountTo7843 : oddPrimeCount 7843 ≤ 990 :=
  smallPrimeAdvanceUpper 7840 3 989 1 0x10b
    smallCountTo7840 (by decide +kernel)

theorem base_7843 : oddPrimeCount 7843 ≤ 990 := smallCountTo7843

set_option maxRecDepth 10000 in
private theorem smallCountTo7875 : oddPrimeCount 7875 ≤ 993 :=
  smallPrimeAdvanceUpper 7843 32 990 3 0x40c10704bc1030400105040c11d041c1030414100040c1110400103
    smallCountTo7843 (by decide +kernel)

theorem base_7875 : oddPrimeCount 7875 ≤ 993 := smallCountTo7875

set_option maxRecDepth 10000 in
private theorem smallCountTo7939 : oddPrimeCount 7939 ≤ 1002 :=
  smallPrimeAdvanceUpper 7875 64 993 9 0x400100040c1000414103041c10d040c10504d41030400107040c100042c10304a4105040c10005641030414100040c10704001030400111
    smallCountTo7875 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8003 : oddPrimeCount 8003 ≤ 1006 :=
  smallPrimeAdvanceUpper 7939 64 1002 4 0x40c10d04141030400100040c1050524103044c100040c11f0434103041c105040c14f045c1030414107040c13d0400103042c113040c135
    smallCountTo7939 (by decide +kernel)

theorem base_8003 : oddPrimeCount 8003 ≤ 1006 := smallCountTo8003

set_option maxRecDepth 10000 in
private theorem smallCountTo8008 : oddPrimeCount 8008 ≤ 1006 :=
  smallPrimeAdvanceUpper 8003 5 1006 0 0x20a08182
    smallCountTo8003 (by decide +kernel)

theorem base_8008 : oddPrimeCount 8008 ≤ 1006 := smallCountTo8008

set_option maxRecDepth 10000 in
private theorem smallCountTo8038 : oddPrimeCount 8038 ≤ 1009 :=
  smallPrimeAdvanceUpper 8008 30 1006 3 0x200081820a0800206086828e081822e083820608e820a08182
    smallCountTo8008 (by decide +kernel)

theorem base_8038 : oddPrimeCount 8038 ≤ 1009 := smallCountTo8038

set_option maxRecDepth 10000 in
private theorem smallCountTo8047 : oddPrimeCount 8047 ≤ 1010 :=
  smallPrimeAdvanceUpper 8038 9 1009 1 0x42c103041410d
    smallCountTo8038 (by decide +kernel)

theorem base_8047 : oddPrimeCount 8047 ≤ 1010 := smallCountTo8047

set_option maxRecDepth 10000 in
private theorem smallCountTo8061 : oddPrimeCount 8061 ≤ 1012 :=
  smallPrimeAdvanceUpper 8047 14 1010 2 0x103054c100040c1070400103
    smallCountTo8047 (by decide +kernel)

theorem base_8061 : oddPrimeCount 8061 ≤ 1012 := smallCountTo8061

set_option maxRecDepth 10000 in
private theorem smallCountTo8074 : oddPrimeCount 8074 ≤ 1013 :=
  smallPrimeAdvanceUpper 8061 13 1012 1 0x2160828206080020e08182
    smallCountTo8061 (by decide +kernel)

theorem base_8074 : oddPrimeCount 8074 ≤ 1013 := smallCountTo8074

set_option maxRecDepth 10000 in
private theorem smallCountTo8088 : oddPrimeCount 8088 ≤ 1015 :=
  smallPrimeAdvanceUpper 8074 14 1013 2 0x28252081820009d820608002
    smallCountTo8074 (by decide +kernel)

theorem base_8088 : oddPrimeCount 8088 ≤ 1015 := smallCountTo8088

set_option maxRecDepth 10000 in
private theorem smallCountTo8152 : oddPrimeCount 8152 ≤ 1022 :=
  smallPrimeAdvanceUpper 8088 64 1015 7 0x81820008282060838200081820a0858206080020e081820008b8206080020a08182160978206082829e081820e0888206080023a08182
    smallCountTo8088 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8216 : oddPrimeCount 8216 ≤ 1028 :=
  smallPrimeAdvanceUpper 8152 64 1022 6 0x3e08282060948200081820a08002060800216081821a0800206083820a08182260800206082820e0818276086820608e8200081825608282
    smallCountTo8152 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8280 : oddPrimeCount 8280 ≤ 1037 :=
  smallPrimeAdvanceUpper 8216 64 1028 9 0x60800200081820a0898206080020008182000838206080020a08182920928206082822e0818216080020608382000818200082820608882
    smallCountTo8216 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8295 : oddPrimeCount 8295 ≤ 1040 :=
  smallPrimeAdvanceUpper 8280 15 1037 3 0x1c1030414100040c1000400103
    smallCountTo8280 (by decide +kernel)

theorem base_8295 : oddPrimeCount 8295 ≤ 1040 := smallCountTo8295

set_option maxRecDepth 10000 in
private theorem smallCountTo8304 : oddPrimeCount 8304 ≤ 1041 :=
  smallPrimeAdvanceUpper 8295 9 1040 1 0x200095820608982
    smallCountTo8295 (by decide +kernel)

theorem base_8304 : oddPrimeCount 8304 ≤ 1041 := smallCountTo8304

set_option maxRecDepth 10000 in
private theorem smallCountTo8307 : oddPrimeCount 8307 ≤ 1041 :=
  smallPrimeAdvanceUpper 8304 3 1041 0 0x14103
    smallCountTo8304 (by decide +kernel)

theorem base_8307 : oddPrimeCount 8307 ≤ 1041 := smallCountTo8307

set_option maxRecDepth 10000 in
private theorem smallCountTo8371 : oddPrimeCount 8371 ≤ 1047 :=
  smallPrimeAdvanceUpper 8307 64 1041 6 0x41c100040c105040010304d4107040c10b04001030434105040c11f044c1030414111040c107040010304f410d040c1000414103040010b
    smallCountTo8307 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8400 : oddPrimeCount 8400 ≤ 1050 :=
  smallPrimeAdvanceUpper 8371 29 1047 3 0x206082820008182220a982060800200081820e082820609282
    smallCountTo8371 (by decide +kernel)

theorem base_8400 : oddPrimeCount 8400 ≤ 1050 := smallCountTo8400

set_option maxRecDepth 10000 in
private theorem smallCountTo8420 : oddPrimeCount 8420 ≤ 1051 :=
  smallPrimeAdvanceUpper 8400 20 1050 1 0x3e081820a0838206086825e081822608002
    smallCountTo8400 (by decide +kernel)

theorem base_8420 : oddPrimeCount 8420 ≤ 1051 := smallCountTo8420

set_option maxRecDepth 10000 in
private theorem smallCountTo8447 : oddPrimeCount 8447 ≤ 1056 :=
  smallPrimeAdvanceUpper 8420 27 1051 5 0xc10004141030400100040c105042c103045c100040c100
    smallCountTo8420 (by decide +kernel)

theorem base_8447 : oddPrimeCount 8447 ≤ 1056 := smallCountTo8447

set_option maxRecDepth 10000 in
private theorem smallCountTo8453 : oddPrimeCount 8453 ≤ 1056 :=
  smallPrimeAdvanceUpper 8447 6 1056 0 0x107040c14f
    smallCountTo8447 (by decide +kernel)

theorem base_8453 : oddPrimeCount 8453 ≤ 1056 := smallCountTo8453

set_option maxRecDepth 10000 in
private theorem smallCountTo8495 : oddPrimeCount 8495 ≤ 1058 :=
  smallPrimeAdvanceUpper 8453 42 1056 2 0x105040c10b04001030414100040c12b0494103041c13d040c11104141030434107040c105
    smallCountTo8453 (by decide +kernel)

theorem base_8495 : oddPrimeCount 8495 ≤ 1058 := smallCountTo8495

set_option maxRecDepth 10000 in
private theorem smallCountTo8547 : oddPrimeCount 8547 ≤ 1065 :=
  smallPrimeAdvanceUpper 8495 52 1058 7 0x474103040010b040c12f050c1030400105040c10704001030414100040c113041c1030400100040c1000414103
    smallCountTo8495 (by decide +kernel)

theorem base_8547 : oddPrimeCount 8547 ≤ 1065 := smallCountTo8547

set_option maxRecDepth 10000 in
private theorem smallCountTo8611 : oddPrimeCount 8611 ≤ 1071 :=
  smallPrimeAdvanceUpper 8547 64 1065 6 0x54c111040c10504ac103041c100040c10d042c1030400105040c1170400103041411f040c10b04341030400100040c1070414103040014f
    smallCountTo8547 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8643 : oddPrimeCount 8643 ≤ 1075 :=
  smallPrimeAdvanceUpper 8611 32 1071 4 0x40c105041c1030494100040c10004001030564105040c1350400103
    smallCountTo8611 (by decide +kernel)

theorem base_8643 : oddPrimeCount 8643 ≤ 1075 := smallCountTo8643

set_option maxRecDepth 10000 in
private theorem smallCountTo8706 : oddPrimeCount 8706 ≤ 1083 :=
  smallPrimeAdvanceUpper 8643 63 1075 8 0x82820008182520888206085820e08182000828206080021a081820a08002060800226081820e0800206080020a0818200083820608282
    smallCountTo8643 (by decide +kernel)

theorem base_8706 : oddPrimeCount 8706 ≤ 1083 := smallCountTo8706

set_option maxRecDepth 10000 in
private theorem smallCountTo8716 : oddPrimeCount 8716 ≤ 1085 :=
  smallPrimeAdvanceUpper 8706 10 1083 2 0x20608f820008182
    smallCountTo8706 (by decide +kernel)

theorem base_8716 : oddPrimeCount 8716 ≤ 1085 := smallCountTo8716

set_option maxRecDepth 10000 in
private theorem smallCountTo8780 : oddPrimeCount 8780 ≤ 1093 :=
  smallPrimeAdvanceUpper 8716 64 1085 8 0x2e0800206085820a081820e0800206082820008182000838206080021a081820008282060898200081820a0858206083823e081828608002
    smallCountTo8716 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo8786 : oddPrimeCount 8786 ≤ 1094 :=
  smallPrimeAdvanceUpper 8780 6 1093 1 0x1820008282
    smallCountTo8780 (by decide +kernel)

theorem base_8786 : oddPrimeCount 8786 ≤ 1094 := smallCountTo8786

set_option maxRecDepth 10000 in
private theorem smallCountTo8816 : oddPrimeCount 8816 ≤ 1096 :=
  smallPrimeAdvanceUpper 8786 30 1094 2 0x1821609d82060828226081821a0800206080022e081820e08282
    smallCountTo8786 (by decide +kernel)

theorem base_8816 : oddPrimeCount 8816 ≤ 1096 := smallCountTo8816

set_option maxRecDepth 10000 in
private theorem smallCountTo8874 : oddPrimeCount 8874 ≤ 1105 :=
  smallPrimeAdvanceUpper 8816 58 1096 9 0x182000800206082820e081820008582060800200081824a0828206080026a081820a088820608002000818200083820608982
    smallCountTo8816 (by decide +kernel)

theorem base_8874 : oddPrimeCount 8874 ≤ 1105 := smallCountTo8874

set_option maxRecDepth 10000 in
private theorem smallCountTo8918 : oddPrimeCount 8918 ≤ 1107 :=
  smallPrimeAdvanceUpper 8874 44 1105 2 0xa081821a0a982060828200081822208002060838216081823a082820609d820e081820a09282
    smallCountTo8874 (by decide +kernel)

theorem base_8918 : oddPrimeCount 8918 ≤ 1107 := smallCountTo8918

set_option maxRecDepth 10000 in
private theorem smallCountTo8925 : oddPrimeCount 8925 ≤ 1108 :=
  smallPrimeAdvanceUpper 8918 7 1107 1 0xc10b0400103
    smallCountTo8918 (by decide +kernel)

theorem base_8925 : oddPrimeCount 8925 ≤ 1108 := smallCountTo8925

set_option maxRecDepth 10000 in
private theorem smallCountTo8977 : oddPrimeCount 8977 ≤ 1115 :=
  smallPrimeAdvanceUpper 8925 52 1108 7 0x53c100040c1000414103041c100040c105045c1030400107040c10d04441030400105040c1000400103041412f
    smallCountTo8925 (by decide +kernel)

theorem base_8977 : oddPrimeCount 8977 ≤ 1115 := smallCountTo8977

set_option maxRecDepth 10000 in
private theorem smallCountTo9040 : oddPrimeCount 9040 ≤ 1121 :=
  smallPrimeAdvanceUpper 8977 63 1115 6 0x81820e086820608582b2081822208282060800200081820a08002060800200081828e08e8206083820a08182000858206082820e08182
    smallCountTo8977 (by decide +kernel)

theorem base_9040 : oddPrimeCount 9040 ≤ 1121 := smallCountTo9040

set_option maxRecDepth 10000 in
private theorem smallCountTo9061 : oddPrimeCount 9061 ≤ 1125 :=
  smallPrimeAdvanceUpper 9040 21 1121 4 0x400103054c100040c10b0414103040010d
    smallCountTo9040 (by decide +kernel)

theorem base_9061 : oddPrimeCount 9061 ≤ 1125 := smallCountTo9061

set_option maxRecDepth 10000 in
private theorem smallCountTo9125 : oddPrimeCount 9125 ≤ 1129 :=
  smallPrimeAdvanceUpper 9061 64 1125 4 0x40c105040010304bc12b040c11d041c103047c105040c13d0400103041410b040c1130400103041c100040c10d0414103042c107040c105
    smallCountTo9061 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9189 : oddPrimeCount 9189 ≤ 1138 :=
  smallPrimeAdvanceUpper 9125 64 1129 9 0x400103045c100040c100043410304a4105040c10704001030414100040c100041c1030564135040c1000414103050c100040c1050400103
    smallCountTo9125 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9234 : oddPrimeCount 9234 ≤ 1143 :=
  smallPrimeAdvanceUpper 9189 45 1138 5 0x20e08e8206088820008182000828206080027a081820a0868206080022e0818200085820608382
    smallCountTo9189 (by decide +kernel)

theorem base_9234 : oddPrimeCount 9234 ≤ 1143 := smallCountTo9234

set_option maxRecDepth 10000 in
private theorem smallCountTo9238 : oddPrimeCount 9238 ≤ 1143 :=
  smallPrimeAdvanceUpper 9234 4 1143 0 0xa08182
    smallCountTo9234 (by decide +kernel)

theorem base_9238 : oddPrimeCount 9238 ≤ 1143 := smallCountTo9238

set_option maxRecDepth 10000 in
private theorem smallCountTo9292 : oddPrimeCount 9292 ≤ 1149 :=
  smallPrimeAdvanceUpper 9238 54 1143 6 0x200081820a083820608582260818200097820609d820a081821a0a48206082820008182000800206092820e08182
    smallCountTo9238 (by decide +kernel)

theorem base_9292 : oddPrimeCount 9292 ≤ 1149 := smallCountTo9292

set_option maxRecDepth 10000 in
private theorem smallCountTo9356 : oddPrimeCount 9356 ≤ 1157 :=
  smallPrimeAdvanceUpper 9292 64 1149 8 0x828206088828e081820a09482060800286081820e0800206080020a081822608382060828200081820008002060868200081825e08282
    smallCountTo9292 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9415 : oddPrimeCount 9415 ≤ 1163 :=
  smallPrimeAdvanceUpper 9356 59 1157 6 0xc107042c1030414111040c100041c1030400153040c10b041410304a4100040c1050400103041c100040c11705841030400105
    smallCountTo9356 (by decide +kernel)

theorem base_9415 : oddPrimeCount 9415 ≤ 1163 := smallCountTo9415

set_option maxRecDepth 10000 in
private theorem smallCountTo9422 : oddPrimeCount 9422 ≤ 1165 :=
  smallPrimeAdvanceUpper 9415 7 1163 2 0x81820008002
    smallCountTo9415 (by decide +kernel)

theorem base_9422 : oddPrimeCount 9422 ≤ 1165 := smallCountTo9422

set_option maxRecDepth 10000 in
private theorem smallCountTo9430 : oddPrimeCount 9430 ≤ 1165 :=
  smallPrimeAdvanceUpper 9422 8 1165 0 0x6082821608182
    smallCountTo9422 (by decide +kernel)

theorem base_9430 : oddPrimeCount 9430 ≤ 1165 := smallCountTo9430

set_option maxRecDepth 10000 in
private theorem smallCountTo9440 : oddPrimeCount 9440 ≤ 1169 :=
  smallPrimeAdvanceUpper 9430 10 1165 4 0x200081820008002
    smallCountTo9430 (by decide +kernel)

theorem base_9440 : oddPrimeCount 9440 ≤ 1169 := smallCountTo9440

set_option maxRecDepth 10000 in
private theorem smallCountTo9504 : oddPrimeCount 9504 ≤ 1176 :=
  smallPrimeAdvanceUpper 9440 64 1169 7 0x6083820a08182160868206082820e081820008002060800222081820008282060800226081820a09a820608002160818200083820608682
    smallCountTo9440 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9568 : oddPrimeCount 9568 ≤ 1182 :=
  smallPrimeAdvanceUpper 9504 64 1176 6 0xa081824a0800206082823e08182000ac8206083821a08182000828206080020e081820a08002060800252081822608582060a4820a08182
    smallCountTo9504 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9578 : oddPrimeCount 9578 ≤ 1182 :=
  smallPrimeAdvanceUpper 9568 10 1182 0 0x38222081820a09e82
    smallCountTo9568 (by decide +kernel)

theorem base_9578 : oddPrimeCount 9578 ≤ 1182 := smallCountTo9578

set_option maxRecDepth 10000 in
private theorem smallCountTo9593 : oddPrimeCount 9593 ≤ 1183 :=
  smallPrimeAdvanceUpper 9578 15 1182 1 0xc10b041c103040012b040c135
    smallCountTo9578 (by decide +kernel)

theorem base_9593 : oddPrimeCount 9593 ≤ 1183 := smallCountTo9593

set_option maxRecDepth 10000 in
private theorem smallCountTo9611 : oddPrimeCount 9611 ≤ 1184 :=
  smallPrimeAdvanceUpper 9593 18 1183 1 0x105040c11d0400103041410d040c107
    smallCountTo9593 (by decide +kernel)

theorem base_9611 : oddPrimeCount 9611 ≤ 1184 := smallCountTo9611

set_option maxRecDepth 10000 in
private theorem smallCountTo9612 : oddPrimeCount 9612 ≤ 1184 :=
  smallPrimeAdvanceUpper 9611 1 1184 0 0x2
    smallCountTo9611 (by decide +kernel)

theorem base_9612 : oddPrimeCount 9612 ≤ 1184 := smallCountTo9612

set_option maxRecDepth 10000 in
private theorem smallCountTo9676 : oddPrimeCount 9676 ≤ 1192 :=
  smallPrimeAdvanceUpper 9612 64 1184 8 0x8182760800206080020a08182000800206082822e081823e08002060858200081820e08282060868200081820a0838206089822208182
    smallCountTo9612 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9732 : oddPrimeCount 9732 ≤ 1198 :=
  smallPrimeAdvanceUpper 9676 56 1192 6 0x80020608b820a08182000858206082820008182b208f8206088820e081821608282060800200081820a0a3820609282
    smallCountTo9676 (by decide +kernel)

theorem base_9732 : oddPrimeCount 9732 ≤ 1198 := smallCountTo9732

set_option maxRecDepth 10000 in
private theorem smallCountTo9754 : oddPrimeCount 9754 ≤ 1202 :=
  smallPrimeAdvanceUpper 9732 22 1198 4 0x206083820008182000828206080020e08182
    smallCountTo9732 (by decide +kernel)

theorem base_9754 : oddPrimeCount 9754 ≤ 1202 := smallCountTo9754

set_option maxRecDepth 10000 in
private theorem smallCountTo9818 : oddPrimeCount 9818 ≤ 1210 :=
  smallPrimeAdvanceUpper 9754 64 1202 8 0xa0858206095821a0818200080020608e820a081820e08002060828200081820008382060b08252081820008282060888200081820a08002
    smallCountTo9754 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9858 : oddPrimeCount 9858 ≤ 1215 :=
  smallPrimeAdvanceUpper 9818 40 1210 5 0x60838216081823e0800206080020a081820008682060828256081820009d820608002
    smallCountTo9818 (by decide +kernel)

theorem base_9858 : oddPrimeCount 9858 ≤ 1215 := smallCountTo9858

set_option maxRecDepth 10000 in
private theorem smallCountTo9922 : oddPrimeCount 9922 ≤ 1221 :=
  smallPrimeAdvanceUpper 9858 64 1215 6 0x81820e08282060a38200081820a0838206094820008182000858206086820a081822608002060828200081821608b8206097820e08182
    smallCountTo9858 (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem smallCountTo9940 : oddPrimeCount 9940 ≤ 1224 :=
  smallPrimeAdvanceUpper 9922 18 1221 3 0x20a08182000800206082822608182
    smallCountTo9922 (by decide +kernel)

theorem base_9940 : oddPrimeCount 9940 ≤ 1224 := smallCountTo9940

set_option maxRecDepth 10000 in
private theorem smallCountTo9948 : oddPrimeCount 9948 ≤ 1225 :=
  smallPrimeAdvanceUpper 9940 8 1224 1 0x9e820608382
    smallCountTo9940 (by decide +kernel)

theorem base_9948 : oddPrimeCount 9948 ≤ 1225 := smallCountTo9948

set_option maxRecDepth 10000 in
private theorem smallCountTo9982 : oddPrimeCount 9982 ≤ 1228 :=
  smallPrimeAdvanceUpper 9948 34 1225 3 0x206092820a081822e08382060828200081821a0800206085822208182
    smallCountTo9948 (by decide +kernel)

theorem base_9982 : oddPrimeCount 9982 ≤ 1228 := smallCountTo9982

set_option maxRecDepth 10000 in
private theorem smallCountTo10000 : oddPrimeCount 10000 ≤ 1228 :=
  smallPrimeAdvanceUpper 9982 18 1228 0 0x21820a081820e0b08206082821a08182
    smallCountTo9982 (by decide +kernel)

theorem base_10000 : oddPrimeCount 10000 ≤ 1228 := smallCountTo10000

end A085265.DyadicPrimeCount

open A085265.DyadicPrimeCount

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem OMA.solution : OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R4.H1 := by
  let packed : ℕ := 0x240c2202040914868d010161c3c000040824040f1a4504028001008071c3d860d8000848ad080a860fc386804070416090e8103c24460405080fc50c01c3404150001828360414122e8000c081264cf040701034101c0409060f0001469000c2002018002c0802080f00018207458c40403000082030001000041226890cc0006000106090407008100c15020e8202408480003102080020080804180a15000040004000300018201c610a0402040f0307010141c2f04038204000040002000300014000e08080612870b4183c0002183200004101e080a00040100818320006061604048284e00010e290003010260007000401008284a0808000302024101c04060000850b00802080b0408840880812143100018000458ae1018020480004000a10280003810580016040400010206ca1100006000180008000c040600028201428620c1e0a06830640008000c0a160000c08221425020101018000e0c0f0202800286094040f000200008205c1c3e000684064000a1024000182048103e0003040603038000a1022061181024101512402e6336728a138c16e1c42234f078c078f8182919348487860b00a1a1324828484882080c131e00824387404050c170080c244e0203090f0100c243c0202070e0285c04020c12020182048040c080c02028102404080409010281010040a0404010281810040a0004020180809ba63
  let seeds : List (ℕ × ℕ) := (List.range 242).scanl (fun q i =>
    let z := (packed >>> (17*i)) % 131072
    (q.1 + z%1024, q.2 + z/1024)) (0,0)
  change ∀ c ∈ seeds, oddPrimeCount c.1 ≤ c.2
  have hdec : seeds = ([(0,0),(611,110),(615,111),(621,113),(629,113),(639,114),(647,117),(657,118),(665,120),(675,121),(683,123),(693,124),(711,126),(719,127),(737,129),(747,131),(771,135),(783,136),(819,140),(825,142),(861,148),(863,149),(909,154),(965,161),(969,162),(1029,171),(1035,173),(1095,182),(1101,183),(1179,192),(1185,193),(1277,205),(1287,207),(1403,221),(1421,222),(1541,241),(1565,245),(1695,263),(1731,268),(1877,287),(1929,292),(2105,316),(2165,325),(2375,350),(2457,362),(2705,392),(2801,407),(3117,442),(3249,456),(3615,504),(3771,524),(4229,578),(4427,601),(5003,669),(5013,671),(5022,672),(5057,675),(5091,679),(5096,679),(5110,682),(5122,684),(5125,684),(5156,686),(5174,688),(5177,688),(5213,692),(5218,692),(5243,696),(5256,696),(5318,703),(5364,707),(5366,707),(5370,707),(5385,708),(5459,720),(5469,720),(5474,721),(5489,724),(5496,724),(5502,725),(5504,726),(5541,731),(5558,732),(5561,732),(5605,737),(5617,737),(5621,737),(5646,740),(5659,745),(5689,748),(5738,753),(5743,755),(5748,755),(5754,756),(5760,756),(5762,756),(5765,756),(5771,756),(5907,776),(5934,778),(5936,778),(5940,779),(5951,779),(5973,780),(5980,780),(6020,784),(6025,784),(6026,784),(6035,785),(6059,789),(6146,800),(6147,800),(6150,800),(6199,805),(6208,806),(6242,810),(6259,812),(6270,814),(6271,815),(6315,820),(6316,820),(6322,821),(6336,823),(6345,825),(6351,825),(6359,827),(6396,832),(6398,833),(6406,833),(6413,833),(6432,835),(6444,835),(6526,842),(6527,842),(6566,847),(6584,851),(6628,854),(6634,854),(6659,857),(6661,858),(6669,858),(6679,860),(6694,862),(6695,862),(6795,874),(6797,874),(6827,877),(6872,884),(6909,887),(6917,889),(6924,889),(6929,889),(6935,889),(6937,889),(6939,889),(6955,891),(6962,893),(7009,900),(7019,902),(7047,905),(7077,907),(7079,908),(7212,920),(7219,922),(7222,922),(7225,922),(7227,922),(7228,922),(7270,927),(7294,928),(7298,929),(7306,929),(7371,937),(7374,937),(7410,938),(7419,940),(7448,941),(7469,944),(7477,945),(7505,949),(7523,952),(7524,952),(7527,952),(7578,961),(7655,970),(7659,970),(7667,970),(7679,972),(7680,972),(7683,973),(7781,984),(7810,986),(7813,986),(7828,988),(7829,989),(7840,989),(7843,990),(7875,993),(8003,1006),(8008,1006),(8038,1009),(8047,1010),(8061,1012),(8074,1013),(8088,1015),(8295,1040),(8304,1041),(8307,1041),(8400,1050),(8420,1051),(8447,1056),(8453,1056),(8495,1058),(8547,1065),(8643,1075),(8706,1083),(8716,1085),(8786,1094),(8816,1096),(8874,1105),(8918,1107),(8925,1108),(8977,1115),(9040,1121),(9061,1125),(9234,1143),(9238,1143),(9292,1149),(9415,1163),(9422,1165),(9430,1165),(9440,1169),(9578,1182),(9593,1183),(9611,1184),(9612,1184),(9732,1198),(9754,1202),(9858,1215),(9940,1224),(9948,1225),(9982,1228),(10000,1228)] : List (ℕ × ℕ)) := by
    dsimp only [seeds, packed] <;> decide +kernel
  rw [hdec]
  refine List.forall_mem_cons.mpr ⟨(by decide +kernel), ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_611, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_615, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_621, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_629, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_639, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_647, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_657, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_665, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_675, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_683, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_693, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_711, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_719, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_737, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_747, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_783, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_819, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_825, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_861, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_863, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_909, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_965, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_969, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1029, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1035, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1095, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1101, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1179, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1185, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1277, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1287, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1403, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1421, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1541, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1565, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1695, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1731, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1877, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_1929, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_2105, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_2165, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_2375, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_2457, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_2705, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_2801, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_3117, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_3249, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_3615, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_3771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_4229, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_4427, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5003, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5013, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5022, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5057, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5091, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5096, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5110, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5122, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5125, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5156, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5174, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5177, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5213, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5218, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5243, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5256, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5318, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5364, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5366, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5370, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5385, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5459, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5469, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5474, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5489, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5496, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5502, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5504, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5541, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5558, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5561, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5605, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5617, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5621, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5646, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5659, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5689, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5738, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5743, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5748, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5754, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5760, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5762, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5765, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5907, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5934, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5936, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5940, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5951, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5973, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_5980, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6020, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6025, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6026, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6035, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6059, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6146, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6147, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6150, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6199, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6208, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6242, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6259, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6270, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6271, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6315, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6316, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6322, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6336, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6345, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6351, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6359, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6396, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6398, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6406, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6413, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6432, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6444, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6526, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6527, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6566, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6584, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6628, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6634, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6659, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6661, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6669, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6679, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6694, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6695, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6795, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6797, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6827, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6872, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6909, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6917, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6924, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6929, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6935, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6937, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6939, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6955, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_6962, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7009, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7019, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7047, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7077, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7079, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7212, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7219, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7222, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7225, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7227, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7228, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7270, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7294, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7298, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7306, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7371, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7374, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7410, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7419, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7448, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7469, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7477, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7505, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7523, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7524, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7527, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7578, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7655, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7659, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7667, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7679, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7680, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7683, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7781, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7810, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7813, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7828, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7829, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7840, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7843, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_7875, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8003, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8008, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8038, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8047, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8061, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8074, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8088, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8295, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8304, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8400, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8420, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8447, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8453, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8495, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8547, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8643, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8706, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8716, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8786, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8816, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8874, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8918, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8925, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_8977, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9040, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9061, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9234, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9238, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9292, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9415, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9422, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9430, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9440, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9578, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9593, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9611, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9612, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9732, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9754, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9858, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9940, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9948, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_9982, ?_⟩
  refine List.forall_mem_cons.mpr ⟨base_10000, ?_⟩
  simp

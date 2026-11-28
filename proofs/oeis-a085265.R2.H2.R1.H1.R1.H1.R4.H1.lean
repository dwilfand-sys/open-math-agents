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
private theorem smallCountTo611 : oddPrimeCount 611 = 110 :=
  smallPrimeAdvance 576 35 104 6 smallCountTo576 (by decide +kernel)

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
private theorem smallCountTo621 : oddPrimeCount 621 = 113 :=
  smallPrimeAdvance 615 6 111 2 smallCountTo615 (by decide +kernel)

theorem base_621 : oddPrimeCount 621 ≤ 113 :=
  (smallCountTo621).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo629 : oddPrimeCount 629 = 113 :=
  smallPrimeAdvance 621 8 113 0 smallCountTo621 (by decide +kernel)

theorem base_629 : oddPrimeCount 629 ≤ 113 :=
  (smallCountTo629).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo639 : oddPrimeCount 639 = 114 :=
  smallPrimeAdvance 629 10 113 1 smallCountTo629 (by decide +kernel)

theorem base_639 : oddPrimeCount 639 ≤ 114 :=
  (smallCountTo639).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo647 : oddPrimeCount 647 = 117 :=
  smallPrimeAdvance 639 8 114 3 smallCountTo639 (by decide +kernel)

theorem base_647 : oddPrimeCount 647 ≤ 117 :=
  (smallCountTo647).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo657 : oddPrimeCount 657 = 118 :=
  smallPrimeAdvance 647 10 117 1 smallCountTo647 (by decide +kernel)

theorem base_657 : oddPrimeCount 657 ≤ 118 :=
  (smallCountTo657).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo665 : oddPrimeCount 665 = 120 :=
  smallPrimeAdvance 657 8 118 2 smallCountTo657 (by decide +kernel)

theorem base_665 : oddPrimeCount 665 ≤ 120 :=
  (smallCountTo665).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo675 : oddPrimeCount 675 = 121 :=
  smallPrimeAdvance 665 10 120 1 smallCountTo665 (by decide +kernel)

theorem base_675 : oddPrimeCount 675 ≤ 121 :=
  (smallCountTo675).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo683 : oddPrimeCount 683 = 123 :=
  smallPrimeAdvance 675 8 121 2 smallCountTo675 (by decide +kernel)

theorem base_683 : oddPrimeCount 683 ≤ 123 :=
  (smallCountTo683).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo693 : oddPrimeCount 693 = 124 :=
  smallPrimeAdvance 683 10 123 1 smallCountTo683 (by decide +kernel)

theorem base_693 : oddPrimeCount 693 ≤ 124 :=
  (smallCountTo693).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo711 : oddPrimeCount 711 = 126 :=
  smallPrimeAdvance 693 18 124 2 smallCountTo693 (by decide +kernel)

theorem base_711 : oddPrimeCount 711 ≤ 126 :=
  (smallCountTo711).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo719 : oddPrimeCount 719 = 127 :=
  smallPrimeAdvance 711 8 126 1 smallCountTo711 (by decide +kernel)

theorem base_719 : oddPrimeCount 719 ≤ 127 :=
  (smallCountTo719).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo737 : oddPrimeCount 737 = 129 :=
  smallPrimeAdvance 719 18 127 2 smallCountTo719 (by decide +kernel)

theorem base_737 : oddPrimeCount 737 ≤ 129 :=
  (smallCountTo737).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo747 : oddPrimeCount 747 = 131 :=
  smallPrimeAdvance 737 10 129 2 smallCountTo737 (by decide +kernel)

theorem base_747 : oddPrimeCount 747 ≤ 131 :=
  (smallCountTo747).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo771 : oddPrimeCount 771 = 135 :=
  smallPrimeAdvance 747 24 131 4 smallCountTo747 (by decide +kernel)

theorem base_771 : oddPrimeCount 771 ≤ 135 :=
  (smallCountTo771).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo783 : oddPrimeCount 783 = 136 :=
  smallPrimeAdvance 771 12 135 1 smallCountTo771 (by decide +kernel)

theorem base_783 : oddPrimeCount 783 ≤ 136 :=
  (smallCountTo783).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo819 : oddPrimeCount 819 = 140 :=
  smallPrimeAdvance 783 36 136 4 smallCountTo783 (by decide +kernel)

theorem base_819 : oddPrimeCount 819 ≤ 140 :=
  (smallCountTo819).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo825 : oddPrimeCount 825 = 142 :=
  smallPrimeAdvance 819 6 140 2 smallCountTo819 (by decide +kernel)

theorem base_825 : oddPrimeCount 825 ≤ 142 :=
  (smallCountTo825).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo861 : oddPrimeCount 861 = 148 :=
  smallPrimeAdvance 825 36 142 6 smallCountTo825 (by decide +kernel)

theorem base_861 : oddPrimeCount 861 ≤ 148 :=
  (smallCountTo861).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo863 : oddPrimeCount 863 = 149 :=
  smallPrimeAdvance 861 2 148 1 smallCountTo861 (by decide +kernel)

theorem base_863 : oddPrimeCount 863 ≤ 149 :=
  (smallCountTo863).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo909 : oddPrimeCount 909 = 154 :=
  smallPrimeAdvance 863 46 149 5 smallCountTo863 (by decide +kernel)

theorem base_909 : oddPrimeCount 909 ≤ 154 :=
  (smallCountTo909).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo965 : oddPrimeCount 965 = 161 :=
  smallPrimeAdvance 909 56 154 7 smallCountTo909 (by decide +kernel)

theorem base_965 : oddPrimeCount 965 ≤ 161 :=
  (smallCountTo965).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo969 : oddPrimeCount 969 = 162 :=
  smallPrimeAdvance 965 4 161 1 smallCountTo965 (by decide +kernel)

theorem base_969 : oddPrimeCount 969 ≤ 162 :=
  (smallCountTo969).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1029 : oddPrimeCount 1029 = 171 :=
  smallPrimeAdvance 969 60 162 9 smallCountTo969 (by decide +kernel)

theorem base_1029 : oddPrimeCount 1029 ≤ 171 :=
  (smallCountTo1029).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1035 : oddPrimeCount 1035 = 173 :=
  smallPrimeAdvance 1029 6 171 2 smallCountTo1029 (by decide +kernel)

theorem base_1035 : oddPrimeCount 1035 ≤ 173 :=
  (smallCountTo1035).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1095 : oddPrimeCount 1095 = 182 :=
  smallPrimeAdvance 1035 60 173 9 smallCountTo1035 (by decide +kernel)

theorem base_1095 : oddPrimeCount 1095 ≤ 182 :=
  (smallCountTo1095).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1101 : oddPrimeCount 1101 = 183 :=
  smallPrimeAdvance 1095 6 182 1 smallCountTo1095 (by decide +kernel)

theorem base_1101 : oddPrimeCount 1101 ≤ 183 :=
  (smallCountTo1101).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1165 : oddPrimeCount 1165 = 191 :=
  smallPrimeAdvance 1101 64 183 8 smallCountTo1101 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1179 : oddPrimeCount 1179 = 192 :=
  smallPrimeAdvance 1165 14 191 1 smallCountTo1165 (by decide +kernel)

theorem base_1179 : oddPrimeCount 1179 ≤ 192 :=
  (smallCountTo1179).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1185 : oddPrimeCount 1185 = 193 :=
  smallPrimeAdvance 1179 6 192 1 smallCountTo1179 (by decide +kernel)

theorem base_1185 : oddPrimeCount 1185 ≤ 193 :=
  (smallCountTo1185).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1249 : oddPrimeCount 1249 = 203 :=
  smallPrimeAdvance 1185 64 193 10 smallCountTo1185 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1277 : oddPrimeCount 1277 = 205 :=
  smallPrimeAdvance 1249 28 203 2 smallCountTo1249 (by decide +kernel)

theorem base_1277 : oddPrimeCount 1277 ≤ 205 :=
  (smallCountTo1277).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1287 : oddPrimeCount 1287 = 207 :=
  smallPrimeAdvance 1277 10 205 2 smallCountTo1277 (by decide +kernel)

theorem base_1287 : oddPrimeCount 1287 ≤ 207 :=
  (smallCountTo1287).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1351 : oddPrimeCount 1351 = 216 :=
  smallPrimeAdvance 1287 64 207 9 smallCountTo1287 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1403 : oddPrimeCount 1403 = 221 :=
  smallPrimeAdvance 1351 52 216 5 smallCountTo1351 (by decide +kernel)

theorem base_1403 : oddPrimeCount 1403 ≤ 221 :=
  (smallCountTo1403).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1421 : oddPrimeCount 1421 = 222 :=
  smallPrimeAdvance 1403 18 221 1 smallCountTo1403 (by decide +kernel)

theorem base_1421 : oddPrimeCount 1421 ≤ 222 :=
  (smallCountTo1421).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1485 : oddPrimeCount 1485 = 234 :=
  smallPrimeAdvance 1421 64 222 12 smallCountTo1421 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1541 : oddPrimeCount 1541 = 241 :=
  smallPrimeAdvance 1485 56 234 7 smallCountTo1485 (by decide +kernel)

theorem base_1541 : oddPrimeCount 1541 ≤ 241 :=
  (smallCountTo1541).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1565 : oddPrimeCount 1565 = 245 :=
  smallPrimeAdvance 1541 24 241 4 smallCountTo1541 (by decide +kernel)

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
private theorem smallCountTo1695 : oddPrimeCount 1695 = 263 :=
  smallPrimeAdvance 1693 2 263 0 smallCountTo1693 (by decide +kernel)

theorem base_1695 : oddPrimeCount 1695 ≤ 263 :=
  (smallCountTo1695).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1731 : oddPrimeCount 1731 = 268 :=
  smallPrimeAdvance 1695 36 263 5 smallCountTo1695 (by decide +kernel)

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
private theorem smallCountTo1877 : oddPrimeCount 1877 = 287 :=
  smallPrimeAdvance 1859 18 282 5 smallCountTo1859 (by decide +kernel)

theorem base_1877 : oddPrimeCount 1877 ≤ 287 :=
  (smallCountTo1877).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo1929 : oddPrimeCount 1929 = 292 :=
  smallPrimeAdvance 1877 52 287 5 smallCountTo1877 (by decide +kernel)

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
private theorem smallCountTo2105 : oddPrimeCount 2105 = 316 :=
  smallPrimeAdvance 2057 48 309 7 smallCountTo2057 (by decide +kernel)

theorem base_2105 : oddPrimeCount 2105 ≤ 316 :=
  (smallCountTo2105).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2165 : oddPrimeCount 2165 = 325 :=
  smallPrimeAdvance 2105 60 316 9 smallCountTo2105 (by decide +kernel)

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
private theorem smallCountTo2375 : oddPrimeCount 2375 = 350 :=
  smallPrimeAdvance 2357 18 349 1 smallCountTo2357 (by decide +kernel)

theorem base_2375 : oddPrimeCount 2375 ≤ 350 :=
  (smallCountTo2375).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2439 : oddPrimeCount 2439 = 360 :=
  smallPrimeAdvance 2375 64 350 10 smallCountTo2375 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2457 : oddPrimeCount 2457 = 362 :=
  smallPrimeAdvance 2439 18 360 2 smallCountTo2439 (by decide +kernel)

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
private theorem smallCountTo2705 : oddPrimeCount 2705 = 392 :=
  smallPrimeAdvance 2649 56 382 10 smallCountTo2649 (by decide +kernel)

theorem base_2705 : oddPrimeCount 2705 ≤ 392 :=
  (smallCountTo2705).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2769 : oddPrimeCount 2769 = 402 :=
  smallPrimeAdvance 2705 64 392 10 smallCountTo2705 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo2801 : oddPrimeCount 2801 = 407 :=
  smallPrimeAdvance 2769 32 402 5 smallCountTo2769 (by decide +kernel)

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
private theorem smallCountTo3117 : oddPrimeCount 3117 = 442 :=
  smallPrimeAdvance 3057 60 436 6 smallCountTo3057 (by decide +kernel)

theorem base_3117 : oddPrimeCount 3117 ≤ 442 :=
  (smallCountTo3117).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3181 : oddPrimeCount 3181 = 449 :=
  smallPrimeAdvance 3117 64 442 7 smallCountTo3117 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3245 : oddPrimeCount 3245 = 456 :=
  smallPrimeAdvance 3181 64 449 7 smallCountTo3181 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3249 : oddPrimeCount 3249 = 456 :=
  smallPrimeAdvance 3245 4 456 0 smallCountTo3245 (by decide +kernel)

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
private theorem smallCountTo3615 : oddPrimeCount 3615 = 504 :=
  smallPrimeAdvance 3569 46 498 6 smallCountTo3569 (by decide +kernel)

theorem base_3615 : oddPrimeCount 3615 ≤ 504 :=
  (smallCountTo3615).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3679 : oddPrimeCount 3679 = 513 :=
  smallPrimeAdvance 3615 64 504 9 smallCountTo3615 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3743 : oddPrimeCount 3743 = 521 :=
  smallPrimeAdvance 3679 64 513 8 smallCountTo3679 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo3771 : oddPrimeCount 3771 = 524 :=
  smallPrimeAdvance 3743 28 521 3 smallCountTo3743 (by decide +kernel)

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
private theorem smallCountTo4229 : oddPrimeCount 4229 = 578 :=
  smallPrimeAdvance 4219 10 577 1 smallCountTo4219 (by decide +kernel)

theorem base_4229 : oddPrimeCount 4229 ≤ 578 :=
  (smallCountTo4229).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4293 : oddPrimeCount 4293 = 588 :=
  smallPrimeAdvance 4229 64 578 10 smallCountTo4229 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4357 : oddPrimeCount 4357 = 594 :=
  smallPrimeAdvance 4293 64 588 6 smallCountTo4293 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4421 : oddPrimeCount 4421 = 600 :=
  smallPrimeAdvance 4357 64 594 6 smallCountTo4357 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo4427 : oddPrimeCount 4427 = 601 :=
  smallPrimeAdvance 4421 6 600 1 smallCountTo4421 (by decide +kernel)

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
private theorem smallCountTo5013 : oddPrimeCount 5013 = 671 :=
  smallPrimeAdvance 5003 10 669 2 smallCountTo5003 (by decide +kernel)

theorem base_5013 : oddPrimeCount 5013 ≤ 671 :=
  (smallCountTo5013).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5022 : oddPrimeCount 5022 = 672 :=
  smallPrimeAdvance 5013 9 671 1 smallCountTo5013 (by decide +kernel)

theorem base_5022 : oddPrimeCount 5022 ≤ 672 :=
  (smallCountTo5022).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5057 : oddPrimeCount 5057 = 675 :=
  smallPrimeAdvance 5022 35 672 3 smallCountTo5022 (by decide +kernel)

theorem base_5057 : oddPrimeCount 5057 ≤ 675 :=
  (smallCountTo5057).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5091 : oddPrimeCount 5091 = 679 :=
  smallPrimeAdvance 5057 34 675 4 smallCountTo5057 (by decide +kernel)

theorem base_5091 : oddPrimeCount 5091 ≤ 679 :=
  (smallCountTo5091).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5096 : oddPrimeCount 5096 = 679 :=
  smallPrimeAdvance 5091 5 679 0 smallCountTo5091 (by decide +kernel)

theorem base_5096 : oddPrimeCount 5096 ≤ 679 :=
  (smallCountTo5096).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5110 : oddPrimeCount 5110 = 682 :=
  smallPrimeAdvance 5096 14 679 3 smallCountTo5096 (by decide +kernel)

theorem base_5110 : oddPrimeCount 5110 ≤ 682 :=
  (smallCountTo5110).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5122 : oddPrimeCount 5122 = 684 :=
  smallPrimeAdvance 5110 12 682 2 smallCountTo5110 (by decide +kernel)

theorem base_5122 : oddPrimeCount 5122 ≤ 684 :=
  (smallCountTo5122).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5125 : oddPrimeCount 5125 = 684 :=
  smallPrimeAdvance 5122 3 684 0 smallCountTo5122 (by decide +kernel)

theorem base_5125 : oddPrimeCount 5125 ≤ 684 :=
  (smallCountTo5125).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5156 : oddPrimeCount 5156 = 686 :=
  smallPrimeAdvance 5125 31 684 2 smallCountTo5125 (by decide +kernel)

theorem base_5156 : oddPrimeCount 5156 ≤ 686 :=
  (smallCountTo5156).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5174 : oddPrimeCount 5174 = 688 :=
  smallPrimeAdvance 5156 18 686 2 smallCountTo5156 (by decide +kernel)

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
private theorem smallCountTo5213 : oddPrimeCount 5213 = 692 :=
  smallPrimeAdvance 5177 36 688 4 smallCountTo5177 (by decide +kernel)

theorem base_5213 : oddPrimeCount 5213 ≤ 692 :=
  (smallCountTo5213).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5218 : oddPrimeCount 5218 = 692 :=
  smallPrimeAdvance 5213 5 692 0 smallCountTo5213 (by decide +kernel)

theorem base_5218 : oddPrimeCount 5218 ≤ 692 :=
  (smallCountTo5218).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5243 : oddPrimeCount 5243 = 696 :=
  smallPrimeAdvance 5218 25 692 4 smallCountTo5218 (by decide +kernel)

theorem base_5243 : oddPrimeCount 5243 ≤ 696 :=
  (smallCountTo5243).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5256 : oddPrimeCount 5256 = 696 :=
  smallPrimeAdvance 5243 13 696 0 smallCountTo5243 (by decide +kernel)

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
private theorem smallCountTo5364 : oddPrimeCount 5364 = 707 :=
  smallPrimeAdvance 5318 46 703 4 smallCountTo5318 (by decide +kernel)

theorem base_5364 : oddPrimeCount 5364 ≤ 707 :=
  (smallCountTo5364).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5366 : oddPrimeCount 5366 = 707 :=
  smallPrimeAdvance 5364 2 707 0 smallCountTo5364 (by decide +kernel)

theorem base_5366 : oddPrimeCount 5366 ≤ 707 :=
  (smallCountTo5366).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5370 : oddPrimeCount 5370 = 707 :=
  smallPrimeAdvance 5366 4 707 0 smallCountTo5366 (by decide +kernel)

theorem base_5370 : oddPrimeCount 5370 ≤ 707 :=
  (smallCountTo5370).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5385 : oddPrimeCount 5385 = 708 :=
  smallPrimeAdvance 5370 15 707 1 smallCountTo5370 (by decide +kernel)

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
private theorem smallCountTo5469 : oddPrimeCount 5469 = 720 :=
  smallPrimeAdvance 5459 10 720 0 smallCountTo5459 (by decide +kernel)

theorem base_5469 : oddPrimeCount 5469 ≤ 720 :=
  (smallCountTo5469).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5474 : oddPrimeCount 5474 = 721 :=
  smallPrimeAdvance 5469 5 720 1 smallCountTo5469 (by decide +kernel)

theorem base_5474 : oddPrimeCount 5474 ≤ 721 :=
  (smallCountTo5474).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5489 : oddPrimeCount 5489 = 724 :=
  smallPrimeAdvance 5474 15 721 3 smallCountTo5474 (by decide +kernel)

theorem base_5489 : oddPrimeCount 5489 ≤ 724 :=
  (smallCountTo5489).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5496 : oddPrimeCount 5496 = 724 :=
  smallPrimeAdvance 5489 7 724 0 smallCountTo5489 (by decide +kernel)

theorem base_5496 : oddPrimeCount 5496 ≤ 724 :=
  (smallCountTo5496).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5502 : oddPrimeCount 5502 = 725 :=
  smallPrimeAdvance 5496 6 724 1 smallCountTo5496 (by decide +kernel)

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
private theorem smallCountTo5558 : oddPrimeCount 5558 = 732 :=
  smallPrimeAdvance 5541 17 731 1 smallCountTo5541 (by decide +kernel)

theorem base_5558 : oddPrimeCount 5558 ≤ 732 :=
  (smallCountTo5558).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5561 : oddPrimeCount 5561 = 732 :=
  smallPrimeAdvance 5558 3 732 0 smallCountTo5558 (by decide +kernel)

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
private theorem smallCountTo5646 : oddPrimeCount 5646 = 740 :=
  smallPrimeAdvance 5621 25 737 3 smallCountTo5621 (by decide +kernel)

theorem base_5646 : oddPrimeCount 5646 ≤ 740 :=
  (smallCountTo5646).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5659 : oddPrimeCount 5659 = 745 :=
  smallPrimeAdvance 5646 13 740 5 smallCountTo5646 (by decide +kernel)

theorem base_5659 : oddPrimeCount 5659 ≤ 745 :=
  (smallCountTo5659).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5689 : oddPrimeCount 5689 = 748 :=
  smallPrimeAdvance 5659 30 745 3 smallCountTo5659 (by decide +kernel)

theorem base_5689 : oddPrimeCount 5689 ≤ 748 :=
  (smallCountTo5689).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5738 : oddPrimeCount 5738 = 753 :=
  smallPrimeAdvance 5689 49 748 5 smallCountTo5689 (by decide +kernel)

theorem base_5738 : oddPrimeCount 5738 ≤ 753 :=
  (smallCountTo5738).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5743 : oddPrimeCount 5743 = 755 :=
  smallPrimeAdvance 5738 5 753 2 smallCountTo5738 (by decide +kernel)

theorem base_5743 : oddPrimeCount 5743 ≤ 755 :=
  (smallCountTo5743).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5748 : oddPrimeCount 5748 = 755 :=
  smallPrimeAdvance 5743 5 755 0 smallCountTo5743 (by decide +kernel)

theorem base_5748 : oddPrimeCount 5748 ≤ 755 :=
  (smallCountTo5748).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5754 : oddPrimeCount 5754 = 756 :=
  smallPrimeAdvance 5748 6 755 1 smallCountTo5748 (by decide +kernel)

theorem base_5754 : oddPrimeCount 5754 ≤ 756 :=
  (smallCountTo5754).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5760 : oddPrimeCount 5760 = 756 :=
  smallPrimeAdvance 5754 6 756 0 smallCountTo5754 (by decide +kernel)

theorem base_5760 : oddPrimeCount 5760 ≤ 756 :=
  (smallCountTo5760).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5762 : oddPrimeCount 5762 = 756 :=
  smallPrimeAdvance 5760 2 756 0 smallCountTo5760 (by decide +kernel)

theorem base_5762 : oddPrimeCount 5762 ≤ 756 :=
  (smallCountTo5762).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5765 : oddPrimeCount 5765 = 756 :=
  smallPrimeAdvance 5762 3 756 0 smallCountTo5762 (by decide +kernel)

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
private theorem smallCountTo5934 : oddPrimeCount 5934 = 778 :=
  smallPrimeAdvance 5907 27 776 2 smallCountTo5907 (by decide +kernel)

theorem base_5934 : oddPrimeCount 5934 ≤ 778 :=
  (smallCountTo5934).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5936 : oddPrimeCount 5936 = 778 :=
  smallPrimeAdvance 5934 2 778 0 smallCountTo5934 (by decide +kernel)

theorem base_5936 : oddPrimeCount 5936 ≤ 778 :=
  (smallCountTo5936).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5940 : oddPrimeCount 5940 = 779 :=
  smallPrimeAdvance 5936 4 778 1 smallCountTo5936 (by decide +kernel)

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
private theorem smallCountTo5973 : oddPrimeCount 5973 = 780 :=
  smallPrimeAdvance 5951 22 779 1 smallCountTo5951 (by decide +kernel)

theorem base_5973 : oddPrimeCount 5973 ≤ 780 :=
  (smallCountTo5973).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo5980 : oddPrimeCount 5980 = 780 :=
  smallPrimeAdvance 5973 7 780 0 smallCountTo5973 (by decide +kernel)

theorem base_5980 : oddPrimeCount 5980 ≤ 780 :=
  (smallCountTo5980).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6020 : oddPrimeCount 6020 = 784 :=
  smallPrimeAdvance 5980 40 780 4 smallCountTo5980 (by decide +kernel)

theorem base_6020 : oddPrimeCount 6020 ≤ 784 :=
  (smallCountTo6020).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6025 : oddPrimeCount 6025 = 784 :=
  smallPrimeAdvance 6020 5 784 0 smallCountTo6020 (by decide +kernel)

theorem base_6025 : oddPrimeCount 6025 ≤ 784 :=
  (smallCountTo6025).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6026 : oddPrimeCount 6026 = 784 :=
  smallPrimeAdvance 6025 1 784 0 smallCountTo6025 (by decide +kernel)

theorem base_6026 : oddPrimeCount 6026 ≤ 784 :=
  (smallCountTo6026).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6035 : oddPrimeCount 6035 = 785 :=
  smallPrimeAdvance 6026 9 784 1 smallCountTo6026 (by decide +kernel)

theorem base_6035 : oddPrimeCount 6035 ≤ 785 :=
  (smallCountTo6035).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6059 : oddPrimeCount 6059 = 789 :=
  smallPrimeAdvance 6035 24 785 4 smallCountTo6035 (by decide +kernel)

theorem base_6059 : oddPrimeCount 6059 ≤ 789 :=
  (smallCountTo6059).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6123 : oddPrimeCount 6123 = 797 :=
  smallPrimeAdvance 6059 64 789 8 smallCountTo6059 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6146 : oddPrimeCount 6146 = 800 :=
  smallPrimeAdvance 6123 23 797 3 smallCountTo6123 (by decide +kernel)

theorem base_6146 : oddPrimeCount 6146 ≤ 800 :=
  (smallCountTo6146).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6147 : oddPrimeCount 6147 = 800 :=
  smallPrimeAdvance 6146 1 800 0 smallCountTo6146 (by decide +kernel)

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
private theorem smallCountTo6199 : oddPrimeCount 6199 = 805 :=
  smallPrimeAdvance 6150 49 800 5 smallCountTo6150 (by decide +kernel)

theorem base_6199 : oddPrimeCount 6199 ≤ 805 :=
  (smallCountTo6199).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6208 : oddPrimeCount 6208 = 806 :=
  smallPrimeAdvance 6199 9 805 1 smallCountTo6199 (by decide +kernel)

theorem base_6208 : oddPrimeCount 6208 ≤ 806 :=
  (smallCountTo6208).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6242 : oddPrimeCount 6242 = 810 :=
  smallPrimeAdvance 6208 34 806 4 smallCountTo6208 (by decide +kernel)

theorem base_6242 : oddPrimeCount 6242 ≤ 810 :=
  (smallCountTo6242).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6259 : oddPrimeCount 6259 = 812 :=
  smallPrimeAdvance 6242 17 810 2 smallCountTo6242 (by decide +kernel)

theorem base_6259 : oddPrimeCount 6259 ≤ 812 :=
  (smallCountTo6259).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6270 : oddPrimeCount 6270 = 814 :=
  smallPrimeAdvance 6259 11 812 2 smallCountTo6259 (by decide +kernel)

theorem base_6270 : oddPrimeCount 6270 ≤ 814 :=
  (smallCountTo6270).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6271 : oddPrimeCount 6271 = 815 :=
  smallPrimeAdvance 6270 1 814 1 smallCountTo6270 (by decide +kernel)

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
private theorem smallCountTo6316 : oddPrimeCount 6316 = 820 :=
  smallPrimeAdvance 6315 1 820 0 smallCountTo6315 (by decide +kernel)

theorem base_6316 : oddPrimeCount 6316 ≤ 820 :=
  (smallCountTo6316).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6322 : oddPrimeCount 6322 = 821 :=
  smallPrimeAdvance 6316 6 820 1 smallCountTo6316 (by decide +kernel)

theorem base_6322 : oddPrimeCount 6322 ≤ 821 :=
  (smallCountTo6322).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6336 : oddPrimeCount 6336 = 823 :=
  smallPrimeAdvance 6322 14 821 2 smallCountTo6322 (by decide +kernel)

theorem base_6336 : oddPrimeCount 6336 ≤ 823 :=
  (smallCountTo6336).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6345 : oddPrimeCount 6345 = 825 :=
  smallPrimeAdvance 6336 9 823 2 smallCountTo6336 (by decide +kernel)

theorem base_6345 : oddPrimeCount 6345 ≤ 825 :=
  (smallCountTo6345).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6351 : oddPrimeCount 6351 = 825 :=
  smallPrimeAdvance 6345 6 825 0 smallCountTo6345 (by decide +kernel)

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
private theorem smallCountTo6396 : oddPrimeCount 6396 = 832 :=
  smallPrimeAdvance 6359 37 827 5 smallCountTo6359 (by decide +kernel)

theorem base_6396 : oddPrimeCount 6396 ≤ 832 :=
  (smallCountTo6396).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6398 : oddPrimeCount 6398 = 833 :=
  smallPrimeAdvance 6396 2 832 1 smallCountTo6396 (by decide +kernel)

theorem base_6398 : oddPrimeCount 6398 ≤ 833 :=
  (smallCountTo6398).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6406 : oddPrimeCount 6406 = 833 :=
  smallPrimeAdvance 6398 8 833 0 smallCountTo6398 (by decide +kernel)

theorem base_6406 : oddPrimeCount 6406 ≤ 833 :=
  (smallCountTo6406).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6413 : oddPrimeCount 6413 = 833 :=
  smallPrimeAdvance 6406 7 833 0 smallCountTo6406 (by decide +kernel)

theorem base_6413 : oddPrimeCount 6413 ≤ 833 :=
  (smallCountTo6413).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6432 : oddPrimeCount 6432 = 835 :=
  smallPrimeAdvance 6413 19 833 2 smallCountTo6413 (by decide +kernel)

theorem base_6432 : oddPrimeCount 6432 ≤ 835 :=
  (smallCountTo6432).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6444 : oddPrimeCount 6444 = 835 :=
  smallPrimeAdvance 6432 12 835 0 smallCountTo6432 (by decide +kernel)

theorem base_6444 : oddPrimeCount 6444 ≤ 835 :=
  (smallCountTo6444).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6508 : oddPrimeCount 6508 = 841 :=
  smallPrimeAdvance 6444 64 835 6 smallCountTo6444 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6526 : oddPrimeCount 6526 = 842 :=
  smallPrimeAdvance 6508 18 841 1 smallCountTo6508 (by decide +kernel)

theorem base_6526 : oddPrimeCount 6526 ≤ 842 :=
  (smallCountTo6526).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6527 : oddPrimeCount 6527 = 842 :=
  smallPrimeAdvance 6526 1 842 0 smallCountTo6526 (by decide +kernel)

theorem base_6527 : oddPrimeCount 6527 ≤ 842 :=
  (smallCountTo6527).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6566 : oddPrimeCount 6566 = 847 :=
  smallPrimeAdvance 6527 39 842 5 smallCountTo6527 (by decide +kernel)

theorem base_6566 : oddPrimeCount 6566 ≤ 847 :=
  (smallCountTo6566).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6584 : oddPrimeCount 6584 = 851 :=
  smallPrimeAdvance 6566 18 847 4 smallCountTo6566 (by decide +kernel)

theorem base_6584 : oddPrimeCount 6584 ≤ 851 :=
  (smallCountTo6584).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6628 : oddPrimeCount 6628 = 854 :=
  smallPrimeAdvance 6584 44 851 3 smallCountTo6584 (by decide +kernel)

theorem base_6628 : oddPrimeCount 6628 ≤ 854 :=
  (smallCountTo6628).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6634 : oddPrimeCount 6634 = 854 :=
  smallPrimeAdvance 6628 6 854 0 smallCountTo6628 (by decide +kernel)

theorem base_6634 : oddPrimeCount 6634 ≤ 854 :=
  (smallCountTo6634).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6659 : oddPrimeCount 6659 = 857 :=
  smallPrimeAdvance 6634 25 854 3 smallCountTo6634 (by decide +kernel)

theorem base_6659 : oddPrimeCount 6659 ≤ 857 :=
  (smallCountTo6659).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6661 : oddPrimeCount 6661 = 858 :=
  smallPrimeAdvance 6659 2 857 1 smallCountTo6659 (by decide +kernel)

theorem base_6661 : oddPrimeCount 6661 ≤ 858 :=
  (smallCountTo6661).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6669 : oddPrimeCount 6669 = 858 :=
  smallPrimeAdvance 6661 8 858 0 smallCountTo6661 (by decide +kernel)

theorem base_6669 : oddPrimeCount 6669 ≤ 858 :=
  (smallCountTo6669).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6679 : oddPrimeCount 6679 = 860 :=
  smallPrimeAdvance 6669 10 858 2 smallCountTo6669 (by decide +kernel)

theorem base_6679 : oddPrimeCount 6679 ≤ 860 :=
  (smallCountTo6679).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6694 : oddPrimeCount 6694 = 862 :=
  smallPrimeAdvance 6679 15 860 2 smallCountTo6679 (by decide +kernel)

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
private theorem smallCountTo6795 : oddPrimeCount 6795 = 874 :=
  smallPrimeAdvance 6759 36 868 6 smallCountTo6759 (by decide +kernel)

theorem base_6795 : oddPrimeCount 6795 ≤ 874 :=
  (smallCountTo6795).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6797 : oddPrimeCount 6797 = 874 :=
  smallPrimeAdvance 6795 2 874 0 smallCountTo6795 (by decide +kernel)

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
private theorem smallCountTo6909 : oddPrimeCount 6909 = 887 :=
  smallPrimeAdvance 6872 37 884 3 smallCountTo6872 (by decide +kernel)

theorem base_6909 : oddPrimeCount 6909 ≤ 887 :=
  (smallCountTo6909).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6917 : oddPrimeCount 6917 = 889 :=
  smallPrimeAdvance 6909 8 887 2 smallCountTo6909 (by decide +kernel)

theorem base_6917 : oddPrimeCount 6917 ≤ 889 :=
  (smallCountTo6917).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6924 : oddPrimeCount 6924 = 889 :=
  smallPrimeAdvance 6917 7 889 0 smallCountTo6917 (by decide +kernel)

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
private theorem smallCountTo6935 : oddPrimeCount 6935 = 889 :=
  smallPrimeAdvance 6929 6 889 0 smallCountTo6929 (by decide +kernel)

theorem base_6935 : oddPrimeCount 6935 ≤ 889 :=
  (smallCountTo6935).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6937 : oddPrimeCount 6937 = 889 :=
  smallPrimeAdvance 6935 2 889 0 smallCountTo6935 (by decide +kernel)

theorem base_6937 : oddPrimeCount 6937 ≤ 889 :=
  (smallCountTo6937).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6939 : oddPrimeCount 6939 = 889 :=
  smallPrimeAdvance 6937 2 889 0 smallCountTo6937 (by decide +kernel)

theorem base_6939 : oddPrimeCount 6939 ≤ 889 :=
  (smallCountTo6939).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo6955 : oddPrimeCount 6955 = 891 :=
  smallPrimeAdvance 6939 16 889 2 smallCountTo6939 (by decide +kernel)

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
private theorem smallCountTo7009 : oddPrimeCount 7009 = 900 :=
  smallPrimeAdvance 6962 47 893 7 smallCountTo6962 (by decide +kernel)

theorem base_7009 : oddPrimeCount 7009 ≤ 900 :=
  (smallCountTo7009).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7019 : oddPrimeCount 7019 = 902 :=
  smallPrimeAdvance 7009 10 900 2 smallCountTo7009 (by decide +kernel)

theorem base_7019 : oddPrimeCount 7019 ≤ 902 :=
  (smallCountTo7019).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7047 : oddPrimeCount 7047 = 905 :=
  smallPrimeAdvance 7019 28 902 3 smallCountTo7019 (by decide +kernel)

theorem base_7047 : oddPrimeCount 7047 ≤ 905 :=
  (smallCountTo7047).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7077 : oddPrimeCount 7077 = 907 :=
  smallPrimeAdvance 7047 30 905 2 smallCountTo7047 (by decide +kernel)

theorem base_7077 : oddPrimeCount 7077 ≤ 907 :=
  (smallCountTo7077).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7079 : oddPrimeCount 7079 = 908 :=
  smallPrimeAdvance 7077 2 907 1 smallCountTo7077 (by decide +kernel)

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
private theorem smallCountTo7212 : oddPrimeCount 7212 = 920 :=
  smallPrimeAdvance 7207 5 919 1 smallCountTo7207 (by decide +kernel)

theorem base_7212 : oddPrimeCount 7212 ≤ 920 :=
  (smallCountTo7212).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7219 : oddPrimeCount 7219 = 922 :=
  smallPrimeAdvance 7212 7 920 2 smallCountTo7212 (by decide +kernel)

theorem base_7219 : oddPrimeCount 7219 ≤ 922 :=
  (smallCountTo7219).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7222 : oddPrimeCount 7222 = 922 :=
  smallPrimeAdvance 7219 3 922 0 smallCountTo7219 (by decide +kernel)

theorem base_7222 : oddPrimeCount 7222 ≤ 922 :=
  (smallCountTo7222).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7225 : oddPrimeCount 7225 = 922 :=
  smallPrimeAdvance 7222 3 922 0 smallCountTo7222 (by decide +kernel)

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
private theorem smallCountTo7270 : oddPrimeCount 7270 = 927 :=
  smallPrimeAdvance 7228 42 922 5 smallCountTo7228 (by decide +kernel)

theorem base_7270 : oddPrimeCount 7270 ≤ 927 :=
  (smallCountTo7270).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7294 : oddPrimeCount 7294 = 928 :=
  smallPrimeAdvance 7270 24 927 1 smallCountTo7270 (by decide +kernel)

theorem base_7294 : oddPrimeCount 7294 ≤ 928 :=
  (smallCountTo7294).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7298 : oddPrimeCount 7298 = 929 :=
  smallPrimeAdvance 7294 4 928 1 smallCountTo7294 (by decide +kernel)

theorem base_7298 : oddPrimeCount 7298 ≤ 929 :=
  (smallCountTo7298).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7306 : oddPrimeCount 7306 = 929 :=
  smallPrimeAdvance 7298 8 929 0 smallCountTo7298 (by decide +kernel)

theorem base_7306 : oddPrimeCount 7306 ≤ 929 :=
  (smallCountTo7306).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7370 : oddPrimeCount 7370 = 937 :=
  smallPrimeAdvance 7306 64 929 8 smallCountTo7306 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7371 : oddPrimeCount 7371 = 937 :=
  smallPrimeAdvance 7370 1 937 0 smallCountTo7370 (by decide +kernel)

theorem base_7371 : oddPrimeCount 7371 ≤ 937 :=
  (smallCountTo7371).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7374 : oddPrimeCount 7374 = 937 :=
  smallPrimeAdvance 7371 3 937 0 smallCountTo7371 (by decide +kernel)

theorem base_7374 : oddPrimeCount 7374 ≤ 937 :=
  (smallCountTo7374).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7410 : oddPrimeCount 7410 = 938 :=
  smallPrimeAdvance 7374 36 937 1 smallCountTo7374 (by decide +kernel)

theorem base_7410 : oddPrimeCount 7410 ≤ 938 :=
  (smallCountTo7410).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7419 : oddPrimeCount 7419 = 940 :=
  smallPrimeAdvance 7410 9 938 2 smallCountTo7410 (by decide +kernel)

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
private theorem smallCountTo7469 : oddPrimeCount 7469 = 944 :=
  smallPrimeAdvance 7448 21 941 3 smallCountTo7448 (by decide +kernel)

theorem base_7469 : oddPrimeCount 7469 ≤ 944 :=
  (smallCountTo7469).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7477 : oddPrimeCount 7477 = 945 :=
  smallPrimeAdvance 7469 8 944 1 smallCountTo7469 (by decide +kernel)

theorem base_7477 : oddPrimeCount 7477 ≤ 945 :=
  (smallCountTo7477).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7505 : oddPrimeCount 7505 = 949 :=
  smallPrimeAdvance 7477 28 945 4 smallCountTo7477 (by decide +kernel)

theorem base_7505 : oddPrimeCount 7505 ≤ 949 :=
  (smallCountTo7505).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7523 : oddPrimeCount 7523 = 952 :=
  smallPrimeAdvance 7505 18 949 3 smallCountTo7505 (by decide +kernel)

theorem base_7523 : oddPrimeCount 7523 ≤ 952 :=
  (smallCountTo7523).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7524 : oddPrimeCount 7524 = 952 :=
  smallPrimeAdvance 7523 1 952 0 smallCountTo7523 (by decide +kernel)

theorem base_7524 : oddPrimeCount 7524 ≤ 952 :=
  (smallCountTo7524).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7527 : oddPrimeCount 7527 = 952 :=
  smallPrimeAdvance 7524 3 952 0 smallCountTo7524 (by decide +kernel)

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
private theorem smallCountTo7655 : oddPrimeCount 7655 = 970 :=
  smallPrimeAdvance 7642 13 968 2 smallCountTo7642 (by decide +kernel)

theorem base_7655 : oddPrimeCount 7655 ≤ 970 :=
  (smallCountTo7655).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7659 : oddPrimeCount 7659 = 970 :=
  smallPrimeAdvance 7655 4 970 0 smallCountTo7655 (by decide +kernel)

theorem base_7659 : oddPrimeCount 7659 ≤ 970 :=
  (smallCountTo7659).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7667 : oddPrimeCount 7667 = 970 :=
  smallPrimeAdvance 7659 8 970 0 smallCountTo7659 (by decide +kernel)

theorem base_7667 : oddPrimeCount 7667 ≤ 970 :=
  (smallCountTo7667).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7679 : oddPrimeCount 7679 = 972 :=
  smallPrimeAdvance 7667 12 970 2 smallCountTo7667 (by decide +kernel)

theorem base_7679 : oddPrimeCount 7679 ≤ 972 :=
  (smallCountTo7679).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7680 : oddPrimeCount 7680 = 972 :=
  smallPrimeAdvance 7679 1 972 0 smallCountTo7679 (by decide +kernel)

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
private theorem smallCountTo7781 : oddPrimeCount 7781 = 984 :=
  smallPrimeAdvance 7747 34 981 3 smallCountTo7747 (by decide +kernel)

theorem base_7781 : oddPrimeCount 7781 ≤ 984 :=
  (smallCountTo7781).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7810 : oddPrimeCount 7810 = 986 :=
  smallPrimeAdvance 7781 29 984 2 smallCountTo7781 (by decide +kernel)

theorem base_7810 : oddPrimeCount 7810 ≤ 986 :=
  (smallCountTo7810).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7813 : oddPrimeCount 7813 = 986 :=
  smallPrimeAdvance 7810 3 986 0 smallCountTo7810 (by decide +kernel)

theorem base_7813 : oddPrimeCount 7813 ≤ 986 :=
  (smallCountTo7813).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7828 : oddPrimeCount 7828 = 988 :=
  smallPrimeAdvance 7813 15 986 2 smallCountTo7813 (by decide +kernel)

theorem base_7828 : oddPrimeCount 7828 ≤ 988 :=
  (smallCountTo7828).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7829 : oddPrimeCount 7829 = 989 :=
  smallPrimeAdvance 7828 1 988 1 smallCountTo7828 (by decide +kernel)

theorem base_7829 : oddPrimeCount 7829 ≤ 989 :=
  (smallCountTo7829).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7840 : oddPrimeCount 7840 = 989 :=
  smallPrimeAdvance 7829 11 989 0 smallCountTo7829 (by decide +kernel)

theorem base_7840 : oddPrimeCount 7840 ≤ 989 :=
  (smallCountTo7840).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo7843 : oddPrimeCount 7843 = 990 :=
  smallPrimeAdvance 7840 3 989 1 smallCountTo7840 (by decide +kernel)

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

theorem base_8003 : oddPrimeCount 8003 ≤ 1006 :=
  (smallCountTo8003).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8008 : oddPrimeCount 8008 = 1006 :=
  smallPrimeAdvance 8003 5 1006 0 smallCountTo8003 (by decide +kernel)

theorem base_8008 : oddPrimeCount 8008 ≤ 1006 :=
  (smallCountTo8008).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8038 : oddPrimeCount 8038 = 1009 :=
  smallPrimeAdvance 8008 30 1006 3 smallCountTo8008 (by decide +kernel)

theorem base_8038 : oddPrimeCount 8038 ≤ 1009 :=
  (smallCountTo8038).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8047 : oddPrimeCount 8047 = 1010 :=
  smallPrimeAdvance 8038 9 1009 1 smallCountTo8038 (by decide +kernel)

theorem base_8047 : oddPrimeCount 8047 ≤ 1010 :=
  (smallCountTo8047).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8061 : oddPrimeCount 8061 = 1012 :=
  smallPrimeAdvance 8047 14 1010 2 smallCountTo8047 (by decide +kernel)

theorem base_8061 : oddPrimeCount 8061 ≤ 1012 :=
  (smallCountTo8061).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8074 : oddPrimeCount 8074 = 1013 :=
  smallPrimeAdvance 8061 13 1012 1 smallCountTo8061 (by decide +kernel)

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
private theorem smallCountTo8295 : oddPrimeCount 8295 = 1040 :=
  smallPrimeAdvance 8280 15 1037 3 smallCountTo8280 (by decide +kernel)

theorem base_8295 : oddPrimeCount 8295 ≤ 1040 :=
  (smallCountTo8295).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8304 : oddPrimeCount 8304 = 1041 :=
  smallPrimeAdvance 8295 9 1040 1 smallCountTo8295 (by decide +kernel)

theorem base_8304 : oddPrimeCount 8304 ≤ 1041 :=
  (smallCountTo8304).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8307 : oddPrimeCount 8307 = 1041 :=
  smallPrimeAdvance 8304 3 1041 0 smallCountTo8304 (by decide +kernel)

theorem base_8307 : oddPrimeCount 8307 ≤ 1041 :=
  (smallCountTo8307).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8371 : oddPrimeCount 8371 = 1047 :=
  smallPrimeAdvance 8307 64 1041 6 smallCountTo8307 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8400 : oddPrimeCount 8400 = 1050 :=
  smallPrimeAdvance 8371 29 1047 3 smallCountTo8371 (by decide +kernel)

theorem base_8400 : oddPrimeCount 8400 ≤ 1050 :=
  (smallCountTo8400).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8420 : oddPrimeCount 8420 = 1051 :=
  smallPrimeAdvance 8400 20 1050 1 smallCountTo8400 (by decide +kernel)

theorem base_8420 : oddPrimeCount 8420 ≤ 1051 :=
  (smallCountTo8420).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8447 : oddPrimeCount 8447 = 1056 :=
  smallPrimeAdvance 8420 27 1051 5 smallCountTo8420 (by decide +kernel)

theorem base_8447 : oddPrimeCount 8447 ≤ 1056 :=
  (smallCountTo8447).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8453 : oddPrimeCount 8453 = 1056 :=
  smallPrimeAdvance 8447 6 1056 0 smallCountTo8447 (by decide +kernel)

theorem base_8453 : oddPrimeCount 8453 ≤ 1056 :=
  (smallCountTo8453).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8495 : oddPrimeCount 8495 = 1058 :=
  smallPrimeAdvance 8453 42 1056 2 smallCountTo8453 (by decide +kernel)

theorem base_8495 : oddPrimeCount 8495 ≤ 1058 :=
  (smallCountTo8495).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8547 : oddPrimeCount 8547 = 1065 :=
  smallPrimeAdvance 8495 52 1058 7 smallCountTo8495 (by decide +kernel)

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
private theorem smallCountTo8706 : oddPrimeCount 8706 = 1083 :=
  smallPrimeAdvance 8643 63 1075 8 smallCountTo8643 (by decide +kernel)

theorem base_8706 : oddPrimeCount 8706 ≤ 1083 :=
  (smallCountTo8706).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8716 : oddPrimeCount 8716 = 1085 :=
  smallPrimeAdvance 8706 10 1083 2 smallCountTo8706 (by decide +kernel)

theorem base_8716 : oddPrimeCount 8716 ≤ 1085 :=
  (smallCountTo8716).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8780 : oddPrimeCount 8780 = 1093 :=
  smallPrimeAdvance 8716 64 1085 8 smallCountTo8716 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8786 : oddPrimeCount 8786 = 1094 :=
  smallPrimeAdvance 8780 6 1093 1 smallCountTo8780 (by decide +kernel)

theorem base_8786 : oddPrimeCount 8786 ≤ 1094 :=
  (smallCountTo8786).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8816 : oddPrimeCount 8816 = 1096 :=
  smallPrimeAdvance 8786 30 1094 2 smallCountTo8786 (by decide +kernel)

theorem base_8816 : oddPrimeCount 8816 ≤ 1096 :=
  (smallCountTo8816).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8874 : oddPrimeCount 8874 = 1105 :=
  smallPrimeAdvance 8816 58 1096 9 smallCountTo8816 (by decide +kernel)

theorem base_8874 : oddPrimeCount 8874 ≤ 1105 :=
  (smallCountTo8874).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8918 : oddPrimeCount 8918 = 1107 :=
  smallPrimeAdvance 8874 44 1105 2 smallCountTo8874 (by decide +kernel)

theorem base_8918 : oddPrimeCount 8918 ≤ 1107 :=
  (smallCountTo8918).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo8925 : oddPrimeCount 8925 = 1108 :=
  smallPrimeAdvance 8918 7 1107 1 smallCountTo8918 (by decide +kernel)

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
private theorem smallCountTo9040 : oddPrimeCount 9040 = 1121 :=
  smallPrimeAdvance 8977 63 1115 6 smallCountTo8977 (by decide +kernel)

theorem base_9040 : oddPrimeCount 9040 ≤ 1121 :=
  (smallCountTo9040).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9061 : oddPrimeCount 9061 = 1125 :=
  smallPrimeAdvance 9040 21 1121 4 smallCountTo9040 (by decide +kernel)

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
private theorem smallCountTo9234 : oddPrimeCount 9234 = 1143 :=
  smallPrimeAdvance 9189 45 1138 5 smallCountTo9189 (by decide +kernel)

theorem base_9234 : oddPrimeCount 9234 ≤ 1143 :=
  (smallCountTo9234).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9238 : oddPrimeCount 9238 = 1143 :=
  smallPrimeAdvance 9234 4 1143 0 smallCountTo9234 (by decide +kernel)

theorem base_9238 : oddPrimeCount 9238 ≤ 1143 :=
  (smallCountTo9238).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9292 : oddPrimeCount 9292 = 1149 :=
  smallPrimeAdvance 9238 54 1143 6 smallCountTo9238 (by decide +kernel)

theorem base_9292 : oddPrimeCount 9292 ≤ 1149 :=
  (smallCountTo9292).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9356 : oddPrimeCount 9356 = 1157 :=
  smallPrimeAdvance 9292 64 1149 8 smallCountTo9292 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9415 : oddPrimeCount 9415 = 1163 :=
  smallPrimeAdvance 9356 59 1157 6 smallCountTo9356 (by decide +kernel)

theorem base_9415 : oddPrimeCount 9415 ≤ 1163 :=
  (smallCountTo9415).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9422 : oddPrimeCount 9422 = 1165 :=
  smallPrimeAdvance 9415 7 1163 2 smallCountTo9415 (by decide +kernel)

theorem base_9422 : oddPrimeCount 9422 ≤ 1165 :=
  (smallCountTo9422).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9430 : oddPrimeCount 9430 = 1165 :=
  smallPrimeAdvance 9422 8 1165 0 smallCountTo9422 (by decide +kernel)

theorem base_9430 : oddPrimeCount 9430 ≤ 1165 :=
  (smallCountTo9430).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9440 : oddPrimeCount 9440 = 1169 :=
  smallPrimeAdvance 9430 10 1165 4 smallCountTo9430 (by decide +kernel)

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
private theorem smallCountTo9578 : oddPrimeCount 9578 = 1182 :=
  smallPrimeAdvance 9568 10 1182 0 smallCountTo9568 (by decide +kernel)

theorem base_9578 : oddPrimeCount 9578 ≤ 1182 :=
  (smallCountTo9578).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9593 : oddPrimeCount 9593 = 1183 :=
  smallPrimeAdvance 9578 15 1182 1 smallCountTo9578 (by decide +kernel)

theorem base_9593 : oddPrimeCount 9593 ≤ 1183 :=
  (smallCountTo9593).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9611 : oddPrimeCount 9611 = 1184 :=
  smallPrimeAdvance 9593 18 1183 1 smallCountTo9593 (by decide +kernel)

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
private theorem smallCountTo9732 : oddPrimeCount 9732 = 1198 :=
  smallPrimeAdvance 9676 56 1192 6 smallCountTo9676 (by decide +kernel)

theorem base_9732 : oddPrimeCount 9732 ≤ 1198 :=
  (smallCountTo9732).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9754 : oddPrimeCount 9754 = 1202 :=
  smallPrimeAdvance 9732 22 1198 4 smallCountTo9732 (by decide +kernel)

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
private theorem smallCountTo9940 : oddPrimeCount 9940 = 1224 :=
  smallPrimeAdvance 9922 18 1221 3 smallCountTo9922 (by decide +kernel)

theorem base_9940 : oddPrimeCount 9940 ≤ 1224 :=
  (smallCountTo9940).le

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem smallCountTo9948 : oddPrimeCount 9948 = 1225 :=
  smallPrimeAdvance 9940 8 1224 1 smallCountTo9940 (by decide +kernel)

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
    dsimp only [seeds, packed]
    decide +kernel
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

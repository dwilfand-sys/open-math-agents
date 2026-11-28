import OMAReductions.R_oeis_a085267_R1_H2_R1_H1_R1
import Mathlib

/-!
Interval coverage and exact profile inequalities for the finite A085267 sieve.
Each interval supplies its strict comparison assuming its own upper bound.
The integer inequalities retain an additional unit for the second representation.
Source: https://oeis.org/A085267
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

open scoped BigOperators

namespace A085267Sieve

def largePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => 2 < p ∧ Nat.Prime p)

def largeRho (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1-1/(p:ℚ))

end A085267Sieve
namespace A085267Moderate

def rows : List (ℕ × ℕ × ℤ) := [
  (300, 305, 225),
  (306, 310, 229),
  (311, 319, 234),
  (320, 328, 241),
  (329, 337, 246),
  (338, 346, 254),
  (347, 359, 261),
  (360, 373, 272),
  (374, 391, 283),
  (392, 412, 296),
  (413, 431, 313),
  (432, 454, 327),
  (455, 482, 345),
  (483, 514, 368),
  (515, 547, 393),
  (548, 589, 419),
  (590, 638, 451),
  (639, 701, 491),
  (702, 770, 539),
  (771, 847, 593),
  (848, 938, 654),
  (939, 1052, 726),
  (1053, 1187, 814),
  (1188, 1352, 923),
  (1353, 1558, 1053),
  (1559, 1807, 1215),
  (1808, 2114, 1413),
  (2115, 2501, 1658),
  (2502, 2808, 1851),
  (2809, 3172, 2082),
  (3173, 3609, 2356),
  (3610, 4147, 2689),
  (4148, 4796, 3094),
  (4797, 5012, 3500),
  (5013, 5242, 3659),
  (5243, 5488, 3828),
  (5489, 5747, 4008),
  (5748, 6034, 4200),
  (6035, 6335, 4409),
  (6336, 6668, 4633),
  (6669, 7018, 4878),
  (7019, 7409, 5136),
  (7410, 7827, 5424),
  (7828, 8494, 5764),
  (8495, 9237, 6259),
  (9238, 9999, 6771),
  (10000, 10353, 7292),
  (10354, 10727, 7550),
  (10728, 11114, 7824),
  (11115, 11519, 8107),
  (11520, 11945, 8403),
  (11946, 12397, 8716),
  (12398, 12862, 9045),
  (12863, 13356, 9387),
  (13357, 13876, 9748),
  (13877, 14422, 10129),
  (14423, 15009, 10531),
  (15010, 15619, 10960),
  (15620, 16798, 11486),
  (16799, 18079, 12355),
  (18080, 19463, 13300),
  (19464, 20438, 14241),
  (20439, 21479, 14959),
  (21480, 22580, 15721),
  (22581, 23741, 16528),
  (23742, 24967, 17379),
  (24968, 26262, 18277),
  (26263, 27634, 19226),
  (27635, 29079, 20232),
  (29080, 30616, 21294),
  (30617, 32242, 22420),
  (32243, 35140, 23788),
  (35141, 38308, 25928),
  (38309, 41241, 28189),
  (41242, 42541, 29073),
  (42542, 43671, 29841),
  (43672, 44833, 30635),
  (44834, 46026, 31451),
  (46027, 47248, 32287),
  (47249, 48199, 32930),
  (48200, 49166, 33594),
  (49167, 50159, 34270),
  (50160, 51167, 34961),
  (51168, 52203, 35664),
  (52204, 53271, 36390),
  (53272, 54359, 37134),
  (54360, 55479, 37895),
  (55480, 56613, 38674),
  (56614, 57775, 39466),
  (57776, 58965, 40276),
  (58966, 60187, 41107),
  (60188, 61431, 41959),
  (61432, 62712, 42828),
  (62713, 64023, 43723),
  (64024, 67574, 44966),
  (67575, 71339, 47465),
  (71340, 75315, 50111),
  (75316, 79515, 52905),
  (79516, 83407, 55774),
  (83408, 87502, 58507),
  (87503, 91798, 61380),
  (91799, 96318, 64397),
  (96319, 101051, 67567),
  (101052, 106038, 70891),
  (106039, 111271, 74389),
  (111272, 116761, 78059),
  (116762, 122530, 81916),
  (122531, 128599, 85964),
  (128600, 139288, 90869),
  (139289, 150873, 98423),
  (150874, 162886, 106531),
  (162887, 175856, 115014),
  (175857, 189863, 124175),
  (189864, 204988, 134067),
  (204989, 221323, 144749),
  (221324, 238981, 156288),
  (238982, 265720, 169903),
  (265721, 295469, 188916),
  (295470, 327979, 209985),
  (327980, 364067, 233090),
  (364068, 404108, 258737),
  (404109, 448564, 287197),
  (448565, 497933, 318796),
  (497934, 567913, 356149),
  (567914, 647169, 406122),
  (647170, 737464, 462796),
  (737465, 808306, 507256),
  (808307, 879578, 551992),
  (879579, 949517, 595873),
  (949518, 1000000, 627559)]

end A085267Moderate

namespace A085267Moderate

open A085267Sieve

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
    (∑ p ∈ A085267Sieve.largePrimeSet (2*j+1), (2*j/(p^2)+1)) ≤
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
  ((∑ p ∈ A085267Sieve.largePrimeSet (2*c.2.1+1), (2*c.2.1/(p^2)+1)) : ℕ) ≤ c.2.2

private theorem endpointCost_of_parts {j a d : ℕ} {c : ℤ}
    (hj : j ≤ 1000000) (hp : oddPrimeCount (2*j+1) ≤ a)
    (hd : (deltaPrimeTable.map (fun p => 2*j/(p^2))).sum = d)
    (hc : ((a+d : ℕ) : ℤ) ≤ c) :
    ((∑ p ∈ A085267Sieve.largePrimeSet (2*j+1), (2*j/(p^2)+1)) : ℕ) ≤ c := by
  have h := totalCostBound j hj
  rw [primeDeltas_list, hd] at h
  exact (Int.ofNat_le.mpr (h.trans (Nat.add_le_add_right hp d))).trans hc


set_option maxRecDepth 20000 in
private theorem endpointCost300 : endpointCostOK (300, 305, 225) := by
  have h611 := base_611
  exact endpointCost_of_parts (j := 305) (a := 110) (d := 115)
    (by decide) h611 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost306 : endpointCostOK (306, 310, 229) := by
  have h621 := base_621
  exact endpointCost_of_parts (j := 310) (a := 113) (d := 116)
    (by decide) h621 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost311 : endpointCostOK (311, 319, 234) := by
  have h639 := base_639
  exact endpointCost_of_parts (j := 319) (a := 114) (d := 120)
    (by decide) h639 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost320 : endpointCostOK (320, 328, 241) := by
  have h657 := base_657
  exact endpointCost_of_parts (j := 328) (a := 118) (d := 123)
    (by decide) h657 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost329 : endpointCostOK (329, 337, 246) := by
  have h675 := base_675
  exact endpointCost_of_parts (j := 337) (a := 121) (d := 125)
    (by decide) h675 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost338 : endpointCostOK (338, 346, 254) := by
  have h693 := base_693
  exact endpointCost_of_parts (j := 346) (a := 124) (d := 130)
    (by decide) h693 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost347 : endpointCostOK (347, 359, 261) := by
  have h719 := base_719
  exact endpointCost_of_parts (j := 359) (a := 127) (d := 134)
    (by decide) h719 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost360 : endpointCostOK (360, 373, 272) := by
  have h747 := base_747
  exact endpointCost_of_parts (j := 373) (a := 131) (d := 141)
    (by decide) h747 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost374 : endpointCostOK (374, 391, 283) := by
  have h783 := base_783
  exact endpointCost_of_parts (j := 391) (a := 136) (d := 147)
    (by decide) h783 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost392 : endpointCostOK (392, 412, 296) := by
  have h825 := base_825
  exact endpointCost_of_parts (j := 412) (a := 142) (d := 154)
    (by decide) h825 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost413 : endpointCostOK (413, 431, 313) := by
  have h863 := base_863
  exact endpointCost_of_parts (j := 431) (a := 149) (d := 164)
    (by decide) h863 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost432 : endpointCostOK (432, 454, 327) := by
  have h909 := base_909
  exact endpointCost_of_parts (j := 454) (a := 154) (d := 173)
    (by decide) h909 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost455 : endpointCostOK (455, 482, 345) := by
  have h965 := base_965
  exact endpointCost_of_parts (j := 482) (a := 161) (d := 184)
    (by decide) h965 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost483 : endpointCostOK (483, 514, 368) := by
  have h1029 := base_1029
  exact endpointCost_of_parts (j := 514) (a := 171) (d := 197)
    (by decide) h1029 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost515 : endpointCostOK (515, 547, 393) := by
  have h1095 := base_1095
  exact endpointCost_of_parts (j := 547) (a := 182) (d := 211)
    (by decide) h1095 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost548 : endpointCostOK (548, 589, 419) := by
  have h1179 := base_1179
  exact endpointCost_of_parts (j := 589) (a := 192) (d := 227)
    (by decide) h1179 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost590 : endpointCostOK (590, 638, 451) := by
  have h1277 := base_1277
  exact endpointCost_of_parts (j := 638) (a := 205) (d := 246)
    (by decide) h1277 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost639 : endpointCostOK (639, 701, 491) := by
  have h1403 := base_1403
  exact endpointCost_of_parts (j := 701) (a := 221) (d := 270)
    (by decide) h1403 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost702 : endpointCostOK (702, 770, 539) := by
  have h1541 := base_1541
  exact endpointCost_of_parts (j := 770) (a := 241) (d := 298)
    (by decide) h1541 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost771 : endpointCostOK (771, 847, 593) := by
  have h1695 := base_1695
  exact endpointCost_of_parts (j := 847) (a := 263) (d := 330)
    (by decide) h1695 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost848 : endpointCostOK (848, 938, 654) := by
  have h1877 := base_1877
  exact endpointCost_of_parts (j := 938) (a := 287) (d := 367)
    (by decide) h1877 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost939 : endpointCostOK (939, 1052, 726) := by
  have h2105 := base_2105
  exact endpointCost_of_parts (j := 1052) (a := 316) (d := 410)
    (by decide) h2105 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1053 : endpointCostOK (1053, 1187, 814) := by
  have h2375 := base_2375
  exact endpointCost_of_parts (j := 1187) (a := 350) (d := 464)
    (by decide) h2375 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1188 : endpointCostOK (1188, 1352, 923) := by
  have h2705 := base_2705
  exact endpointCost_of_parts (j := 1352) (a := 392) (d := 531)
    (by decide) h2705 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1353 : endpointCostOK (1353, 1558, 1053) := by
  have h3117 := base_3117
  exact endpointCost_of_parts (j := 1558) (a := 442) (d := 611)
    (by decide) h3117 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1559 : endpointCostOK (1559, 1807, 1215) := by
  have h3615 := base_3615
  exact endpointCost_of_parts (j := 1807) (a := 504) (d := 711)
    (by decide) h3615 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost1808 : endpointCostOK (1808, 2114, 1413) := by
  have h4229 := base_4229
  exact endpointCost_of_parts (j := 2114) (a := 578) (d := 835)
    (by decide) h4229 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost2115 : endpointCostOK (2115, 2501, 1658) := by
  have h5003 := base_5003
  exact endpointCost_of_parts (j := 2501) (a := 669) (d := 989)
    (by decide) h5003 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost2502 : endpointCostOK (2502, 2808, 1851) := by
  have h5617 := base_5617
  exact endpointCost_of_parts (j := 2808) (a := 737) (d := 1114)
    (by decide) h5617 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost2809 : endpointCostOK (2809, 3172, 2082) := by
  have h6345 := base_6345
  exact endpointCost_of_parts (j := 3172) (a := 825) (d := 1257)
    (by decide) h6345 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost3173 : endpointCostOK (3173, 3609, 2356) := by
  have h7219 := base_7219
  exact endpointCost_of_parts (j := 3609) (a := 922) (d := 1434)
    (by decide) h7219 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost3610 : endpointCostOK (3610, 4147, 2689) := by
  have h8295 := base_8295
  exact endpointCost_of_parts (j := 4147) (a := 1040) (d := 1649)
    (by decide) h8295 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost4148 : endpointCostOK (4148, 4796, 3094) := by
  have h9593 := base_9593
  exact endpointCost_of_parts (j := 4796) (a := 1183) (d := 1911)
    (by decide) h9593 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost4797 : endpointCostOK (4797, 5012, 3500) := by
  have h5013 := base_5013
  have h10025 : oddPrimeCount 10025 ≤ 1506 :=
    liftCount (m := 5013) (e := 12) (a := 671) (by decide) (by decide) (by decide) (by decide) (by decide) h5013
  exact endpointCost_of_parts (j := 5012) (a := 1506) (d := 1994)
    (by decide) h10025 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5013 : endpointCostOK (5013, 5242, 3659) := by
  have h5243 := base_5243
  have h10485 : oddPrimeCount 10485 ≤ 1569 :=
    liftCount (m := 5243) (e := 12) (a := 696) (by decide) (by decide) (by decide) (by decide) (by decide) h5243
  exact endpointCost_of_parts (j := 5242) (a := 1569) (d := 2090)
    (by decide) h10485 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5243 : endpointCostOK (5243, 5488, 3828) := by
  have h5489 := base_5489
  have h10977 : oddPrimeCount 10977 ≤ 1638 :=
    liftCount (m := 5489) (e := 12) (a := 724) (by decide) (by decide) (by decide) (by decide) (by decide) h5489
  exact endpointCost_of_parts (j := 5488) (a := 1638) (d := 2190)
    (by decide) h10977 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5489 : endpointCostOK (5489, 5747, 4008) := by
  have h5748 := base_5748
  have h11495 : oddPrimeCount 11495 ≤ 1713 :=
    liftCount (m := 5748) (e := 12) (a := 755) (by decide) (by decide) (by decide) (by decide) (by decide) h5748
  exact endpointCost_of_parts (j := 5747) (a := 1713) (d := 2295)
    (by decide) h11495 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost5748 : endpointCostOK (5748, 6034, 4200) := by
  have h6035 := base_6035
  have h12069 : oddPrimeCount 12069 ≤ 1790 :=
    liftCount (m := 6035) (e := 12) (a := 785) (by decide) (by decide) (by decide) (by decide) (by decide) h6035
  exact endpointCost_of_parts (j := 6034) (a := 1790) (d := 2410)
    (by decide) h12069 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost6035 : endpointCostOK (6035, 6335, 4409) := by
  have h6336 := base_6336
  have h12671 : oddPrimeCount 12671 ≤ 1879 :=
    liftCount (m := 6336) (e := 12) (a := 823) (by decide) (by decide) (by decide) (by decide) (by decide) h6336
  exact endpointCost_of_parts (j := 6335) (a := 1879) (d := 2530)
    (by decide) h12671 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost6336 : endpointCostOK (6336, 6668, 4633) := by
  have h6669 := base_6669
  have h13337 : oddPrimeCount 13337 ≤ 1969 :=
    liftCount (m := 6669) (e := 12) (a := 858) (by decide) (by decide) (by decide) (by decide) (by decide) h6669
  exact endpointCost_of_parts (j := 6668) (a := 1969) (d := 2664)
    (by decide) h13337 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost6669 : endpointCostOK (6669, 7018, 4878) := by
  have h7019 := base_7019
  have h14037 : oddPrimeCount 14037 ≤ 2071 :=
    liftCount (m := 7019) (e := 12) (a := 902) (by decide) (by decide) (by decide) (by decide) (by decide) h7019
  exact endpointCost_of_parts (j := 7018) (a := 2071) (d := 2807)
    (by decide) h14037 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost7019 : endpointCostOK (7019, 7409, 5136) := by
  have h7410 := base_7410
  have h14819 : oddPrimeCount 14819 ≤ 2173 :=
    liftCount (m := 7410) (e := 12) (a := 938) (by decide) (by decide) (by decide) (by decide) (by decide) h7410
  exact endpointCost_of_parts (j := 7409) (a := 2173) (d := 2963)
    (by decide) h14819 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost7410 : endpointCostOK (7410, 7827, 5424) := by
  have h7828 := base_7828
  have h15655 : oddPrimeCount 15655 ≤ 2292 :=
    liftCount (m := 7828) (e := 12) (a := 988) (by decide) (by decide) (by decide) (by decide) (by decide) h7828
  exact endpointCost_of_parts (j := 7827) (a := 2292) (d := 3132)
    (by decide) h15655 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost7828 : endpointCostOK (7828, 8494, 5764) := by
  have h8495 := base_8495
  have h16989 : oddPrimeCount 16989 ≤ 2364 :=
    liftCount (m := 8495) (e := 13) (a := 1058) (by decide) (by decide) (by decide) (by decide) (by decide) h8495
  exact endpointCost_of_parts (j := 8494) (a := 2364) (d := 3400)
    (by decide) h16989 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost8495 : endpointCostOK (8495, 9237, 6259) := by
  have h9238 := base_9238
  have h18475 : oddPrimeCount 18475 ≤ 2564 :=
    liftCount (m := 9238) (e := 13) (a := 1143) (by decide) (by decide) (by decide) (by decide) (by decide) h9238
  exact endpointCost_of_parts (j := 9237) (a := 2564) (d := 3695)
    (by decide) h18475 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost9238 : endpointCostOK (9238, 9999, 6771) := by
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
private theorem endpointCost10354 : endpointCostOK (10354, 10727, 7550) := by
  have h5364 := base_5364
  have h10728 : oddPrimeCount 10728 ≤ 1601 :=
    liftCount (m := 5364) (e := 12) (a := 707) (by decide) (by decide) (by decide) (by decide) (by decide) h5364
  have h21455 : oddPrimeCount 21455 ≤ 3251 :=
    liftCount (m := 10728) (e := 13) (a := 1601) (by decide) (by decide) (by decide) (by decide) (by decide) h10728
  exact endpointCost_of_parts (j := 10727) (a := 3251) (d := 4299)
    (by decide) h21455 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost10728 : endpointCostOK (10728, 11114, 7824) := by
  have h5558 := base_5558
  have h11115 : oddPrimeCount 11115 ≤ 1658 :=
    liftCount (m := 5558) (e := 12) (a := 732) (by decide) (by decide) (by decide) (by decide) (by decide) h5558
  have h22229 : oddPrimeCount 22229 ≤ 3368 :=
    liftCount (m := 11115) (e := 13) (a := 1658) (by decide) (by decide) (by decide) (by decide) (by decide) h11115
  exact endpointCost_of_parts (j := 11114) (a := 3368) (d := 4456)
    (by decide) h22229 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost11115 : endpointCostOK (11115, 11519, 8107) := by
  have h5760 := base_5760
  have h11520 : oddPrimeCount 11520 ≤ 1716 :=
    liftCount (m := 5760) (e := 12) (a := 756) (by decide) (by decide) (by decide) (by decide) (by decide) h5760
  have h23039 : oddPrimeCount 23039 ≤ 3488 :=
    liftCount (m := 11520) (e := 13) (a := 1716) (by decide) (by decide) (by decide) (by decide) (by decide) h11520
  exact endpointCost_of_parts (j := 11519) (a := 3488) (d := 4619)
    (by decide) h23039 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost11520 : endpointCostOK (11520, 11945, 8403) := by
  have h5973 := base_5973
  have h11946 : oddPrimeCount 11946 ≤ 1775 :=
    liftCount (m := 5973) (e := 12) (a := 780) (by decide) (by decide) (by decide) (by decide) (by decide) h5973
  have h23891 : oddPrimeCount 23891 ≤ 3612 :=
    liftCount (m := 11946) (e := 13) (a := 1775) (by decide) (by decide) (by decide) (by decide) (by decide) h11946
  exact endpointCost_of_parts (j := 11945) (a := 3612) (d := 4791)
    (by decide) h23891 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost11946 : endpointCostOK (11946, 12397, 8716) := by
  have h6199 := base_6199
  have h12398 : oddPrimeCount 12398 ≤ 1838 :=
    liftCount (m := 6199) (e := 12) (a := 805) (by decide) (by decide) (by decide) (by decide) (by decide) h6199
  have h24795 : oddPrimeCount 24795 ≤ 3745 :=
    liftCount (m := 12398) (e := 13) (a := 1838) (by decide) (by decide) (by decide) (by decide) (by decide) h12398
  exact endpointCost_of_parts (j := 12397) (a := 3745) (d := 4971)
    (by decide) h24795 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost12398 : endpointCostOK (12398, 12862, 9045) := by
  have h6432 := base_6432
  have h12863 : oddPrimeCount 12863 ≤ 1907 :=
    liftCount (m := 6432) (e := 12) (a := 835) (by decide) (by decide) (by decide) (by decide) (by decide) h6432
  have h25725 : oddPrimeCount 25725 ≤ 3885 :=
    liftCount (m := 12863) (e := 13) (a := 1907) (by decide) (by decide) (by decide) (by decide) (by decide) h12863
  exact endpointCost_of_parts (j := 12862) (a := 3885) (d := 5160)
    (by decide) h25725 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost12863 : endpointCostOK (12863, 13356, 9387) := by
  have h6679 := base_6679
  have h13357 : oddPrimeCount 13357 ≤ 1973 :=
    liftCount (m := 6679) (e := 12) (a := 860) (by decide) (by decide) (by decide) (by decide) (by decide) h6679
  have h26713 : oddPrimeCount 26713 ≤ 4027 :=
    liftCount (m := 13357) (e := 13) (a := 1973) (by decide) (by decide) (by decide) (by decide) (by decide) h13357
  exact endpointCost_of_parts (j := 13356) (a := 4027) (d := 5360)
    (by decide) h26713 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost13357 : endpointCostOK (13357, 13876, 9748) := by
  have h6939 := base_6939
  have h13877 : oddPrimeCount 13877 ≤ 2045 :=
    liftCount (m := 6939) (e := 12) (a := 889) (by decide) (by decide) (by decide) (by decide) (by decide) h6939
  have h27753 : oddPrimeCount 27753 ≤ 4179 :=
    liftCount (m := 13877) (e := 13) (a := 2045) (by decide) (by decide) (by decide) (by decide) (by decide) h13877
  exact endpointCost_of_parts (j := 13876) (a := 4179) (d := 5569)
    (by decide) h27753 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost13877 : endpointCostOK (13877, 14422, 10129) := by
  have h7212 := base_7212
  have h14423 : oddPrimeCount 14423 ≤ 2122 :=
    liftCount (m := 7212) (e := 12) (a := 920) (by decide) (by decide) (by decide) (by decide) (by decide) h7212
  have h28845 : oddPrimeCount 28845 ≤ 4340 :=
    liftCount (m := 14423) (e := 13) (a := 2122) (by decide) (by decide) (by decide) (by decide) (by decide) h14423
  exact endpointCost_of_parts (j := 14422) (a := 4340) (d := 5789)
    (by decide) h28845 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost14423 : endpointCostOK (14423, 15009, 10531) := by
  have h7505 := base_7505
  have h15010 : oddPrimeCount 15010 ≤ 2199 :=
    liftCount (m := 7505) (e := 12) (a := 949) (by decide) (by decide) (by decide) (by decide) (by decide) h7505
  have h30019 : oddPrimeCount 30019 ≤ 4508 :=
    liftCount (m := 15010) (e := 13) (a := 2199) (by decide) (by decide) (by decide) (by decide) (by decide) h15010
  exact endpointCost_of_parts (j := 15009) (a := 4508) (d := 6023)
    (by decide) h30019 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost15010 : endpointCostOK (15010, 15619, 10960) := by
  have h7810 := base_7810
  have h15620 : oddPrimeCount 15620 ≤ 2287 :=
    liftCount (m := 7810) (e := 12) (a := 986) (by decide) (by decide) (by decide) (by decide) (by decide) h7810
  have h31239 : oddPrimeCount 31239 ≤ 4690 :=
    liftCount (m := 15620) (e := 13) (a := 2287) (by decide) (by decide) (by decide) (by decide) (by decide) h15620
  exact endpointCost_of_parts (j := 15619) (a := 4690) (d := 6270)
    (by decide) h31239 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost15620 : endpointCostOK (15620, 16798, 11486) := by
  have h8400 := base_8400
  have h16799 : oddPrimeCount 16799 ≤ 2342 :=
    liftCount (m := 8400) (e := 13) (a := 1050) (by decide) (by decide) (by decide) (by decide) (by decide) h8400
  have h33597 : oddPrimeCount 33597 ≤ 4741 :=
    liftCount (m := 16799) (e := 14) (a := 2342) (by decide) (by decide) (by decide) (by decide) (by decide) h16799
  exact endpointCost_of_parts (j := 16798) (a := 4741) (d := 6745)
    (by decide) h33597 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost16799 : endpointCostOK (16799, 18079, 12355) := by
  have h9040 := base_9040
  have h18080 : oddPrimeCount 18080 ≤ 2511 :=
    liftCount (m := 9040) (e := 13) (a := 1121) (by decide) (by decide) (by decide) (by decide) (by decide) h9040
  have h36159 : oddPrimeCount 36159 ≤ 5093 :=
    liftCount (m := 18080) (e := 14) (a := 2511) (by decide) (by decide) (by decide) (by decide) (by decide) h18080
  exact endpointCost_of_parts (j := 18079) (a := 5093) (d := 7262)
    (by decide) h36159 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost18080 : endpointCostOK (18080, 19463, 13300) := by
  have h9732 := base_9732
  have h19464 : oddPrimeCount 19464 ≤ 2695 :=
    liftCount (m := 9732) (e := 13) (a := 1198) (by decide) (by decide) (by decide) (by decide) (by decide) h9732
  have h38927 : oddPrimeCount 38927 ≤ 5475 :=
    liftCount (m := 19464) (e := 14) (a := 2695) (by decide) (by decide) (by decide) (by decide) (by decide) h19464
  exact endpointCost_of_parts (j := 19463) (a := 5475) (d := 7825)
    (by decide) h38927 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost19464 : endpointCostOK (19464, 20438, 14241) := by
  have h5110 := base_5110
  have h10220 : oddPrimeCount 10220 ≤ 1533 :=
    liftCount (m := 5110) (e := 12) (a := 682) (by decide) (by decide) (by decide) (by decide) (by decide) h5110
  have h20439 : oddPrimeCount 20439 ≤ 3105 :=
    liftCount (m := 10220) (e := 13) (a := 1533) (by decide) (by decide) (by decide) (by decide) (by decide) h10220
  have h40877 : oddPrimeCount 40877 ≤ 6024 :=
    liftCount (m := 20439) (e := 14) (a := 3105) (by decide) (by decide) (by decide) (by decide) (by decide) h20439
  exact endpointCost_of_parts (j := 20438) (a := 6024) (d := 8217)
    (by decide) h40877 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost20439 : endpointCostOK (20439, 21479, 14959) := by
  have h5370 := base_5370
  have h10740 : oddPrimeCount 10740 ≤ 1602 :=
    liftCount (m := 5370) (e := 12) (a := 707) (by decide) (by decide) (by decide) (by decide) (by decide) h5370
  have h21480 : oddPrimeCount 21480 ≤ 3254 :=
    liftCount (m := 10740) (e := 13) (a := 1602) (by decide) (by decide) (by decide) (by decide) (by decide) h10740
  have h42959 : oddPrimeCount 42959 ≤ 6322 :=
    liftCount (m := 21480) (e := 14) (a := 3254) (by decide) (by decide) (by decide) (by decide) (by decide) h21480
  exact endpointCost_of_parts (j := 21479) (a := 6322) (d := 8637)
    (by decide) h42959 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost21480 : endpointCostOK (21480, 22580, 15721) := by
  have h5646 := base_5646
  have h11291 : oddPrimeCount 11291 ≤ 1681 :=
    liftCount (m := 5646) (e := 12) (a := 740) (by decide) (by decide) (by decide) (by decide) (by decide) h5646
  have h22581 : oddPrimeCount 22581 ≤ 3418 :=
    liftCount (m := 11291) (e := 13) (a := 1681) (by decide) (by decide) (by decide) (by decide) (by decide) h11291
  have h45161 : oddPrimeCount 45161 ≤ 6643 :=
    liftCount (m := 22581) (e := 14) (a := 3418) (by decide) (by decide) (by decide) (by decide) (by decide) h22581
  exact endpointCost_of_parts (j := 22580) (a := 6643) (d := 9078)
    (by decide) h45161 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost22581 : endpointCostOK (22581, 23741, 16528) := by
  have h5936 := base_5936
  have h11871 : oddPrimeCount 11871 ≤ 1767 :=
    liftCount (m := 5936) (e := 12) (a := 778) (by decide) (by decide) (by decide) (by decide) (by decide) h5936
  have h23742 : oddPrimeCount 23742 ≤ 3593 :=
    liftCount (m := 11871) (e := 13) (a := 1767) (by decide) (by decide) (by decide) (by decide) (by decide) h11871
  have h47483 : oddPrimeCount 47483 ≤ 6984 :=
    liftCount (m := 23742) (e := 14) (a := 3593) (by decide) (by decide) (by decide) (by decide) (by decide) h23742
  exact endpointCost_of_parts (j := 23741) (a := 6984) (d := 9544)
    (by decide) h47483 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost23742 : endpointCostOK (23742, 24967, 17379) := by
  have h6242 := base_6242
  have h12484 : oddPrimeCount 12484 ≤ 1850 :=
    liftCount (m := 6242) (e := 12) (a := 810) (by decide) (by decide) (by decide) (by decide) (by decide) h6242
  have h24968 : oddPrimeCount 24968 ≤ 3770 :=
    liftCount (m := 12484) (e := 13) (a := 1850) (by decide) (by decide) (by decide) (by decide) (by decide) h12484
  have h49935 : oddPrimeCount 49935 ≤ 7336 :=
    liftCount (m := 24968) (e := 14) (a := 3770) (by decide) (by decide) (by decide) (by decide) (by decide) h24968
  exact endpointCost_of_parts (j := 24967) (a := 7336) (d := 10043)
    (by decide) h49935 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost24968 : endpointCostOK (24968, 26262, 18277) := by
  have h6566 := base_6566
  have h13132 : oddPrimeCount 13132 ≤ 1941 :=
    liftCount (m := 6566) (e := 12) (a := 847) (by decide) (by decide) (by decide) (by decide) (by decide) h6566
  have h26263 : oddPrimeCount 26263 ≤ 3961 :=
    liftCount (m := 13132) (e := 13) (a := 1941) (by decide) (by decide) (by decide) (by decide) (by decide) h13132
  have h52525 : oddPrimeCount 52525 ≤ 7712 :=
    liftCount (m := 26263) (e := 14) (a := 3961) (by decide) (by decide) (by decide) (by decide) (by decide) h26263
  exact endpointCost_of_parts (j := 26262) (a := 7712) (d := 10565)
    (by decide) h52525 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost26263 : endpointCostOK (26263, 27634, 19226) := by
  have h6909 := base_6909
  have h13818 : oddPrimeCount 13818 ≤ 2038 :=
    liftCount (m := 6909) (e := 12) (a := 887) (by decide) (by decide) (by decide) (by decide) (by decide) h6909
  have h27635 : oddPrimeCount 27635 ≤ 4163 :=
    liftCount (m := 13818) (e := 13) (a := 2038) (by decide) (by decide) (by decide) (by decide) (by decide) h13818
  have h55269 : oddPrimeCount 55269 ≤ 8110 :=
    liftCount (m := 27635) (e := 14) (a := 4163) (by decide) (by decide) (by decide) (by decide) (by decide) h27635
  exact endpointCost_of_parts (j := 27634) (a := 8110) (d := 11116)
    (by decide) h55269 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost27635 : endpointCostOK (27635, 29079, 20232) := by
  have h7270 := base_7270
  have h14540 : oddPrimeCount 14540 ≤ 2138 :=
    liftCount (m := 7270) (e := 12) (a := 927) (by decide) (by decide) (by decide) (by decide) (by decide) h7270
  have h29080 : oddPrimeCount 29080 ≤ 4374 :=
    liftCount (m := 14540) (e := 13) (a := 2138) (by decide) (by decide) (by decide) (by decide) (by decide) h14540
  have h58159 : oddPrimeCount 58159 ≤ 8528 :=
    liftCount (m := 29080) (e := 14) (a := 4374) (by decide) (by decide) (by decide) (by decide) (by decide) h29080
  exact endpointCost_of_parts (j := 29079) (a := 8528) (d := 11704)
    (by decide) h58159 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost29080 : endpointCostOK (29080, 30616, 21294) := by
  have h7655 := base_7655
  have h15309 : oddPrimeCount 15309 ≤ 2245 :=
    liftCount (m := 7655) (e := 12) (a := 970) (by decide) (by decide) (by decide) (by decide) (by decide) h7655
  have h30617 : oddPrimeCount 30617 ≤ 4600 :=
    liftCount (m := 15309) (e := 13) (a := 2245) (by decide) (by decide) (by decide) (by decide) (by decide) h15309
  have h61233 : oddPrimeCount 61233 ≤ 8973 :=
    liftCount (m := 30617) (e := 14) (a := 4600) (by decide) (by decide) (by decide) (by decide) (by decide) h30617
  exact endpointCost_of_parts (j := 30616) (a := 8973) (d := 12321)
    (by decide) h61233 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost30617 : endpointCostOK (30617, 32242, 22420) := by
  have h8061 := base_8061
  have h16122 : oddPrimeCount 16122 ≤ 2355 :=
    liftCount (m := 8061) (e := 12) (a := 1012) (by decide) (by decide) (by decide) (by decide) (by decide) h8061
  have h32243 : oddPrimeCount 32243 ≤ 4835 :=
    liftCount (m := 16122) (e := 13) (a := 2355) (by decide) (by decide) (by decide) (by decide) (by decide) h16122
  have h64485 : oddPrimeCount 64485 ≤ 9441 :=
    liftCount (m := 32243) (e := 14) (a := 4835) (by decide) (by decide) (by decide) (by decide) (by decide) h32243
  exact endpointCost_of_parts (j := 32242) (a := 9441) (d := 12979)
    (by decide) h64485 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost32243 : endpointCostOK (32243, 35140, 23788) := by
  have h8786 := base_8786
  have h17571 : oddPrimeCount 17571 ≤ 2445 :=
    liftCount (m := 8786) (e := 13) (a := 1094) (by decide) (by decide) (by decide) (by decide) (by decide) h8786
  have h35141 : oddPrimeCount 35141 ≤ 4955 :=
    liftCount (m := 17571) (e := 14) (a := 2445) (by decide) (by decide) (by decide) (by decide) (by decide) h17571
  have h70281 : oddPrimeCount 70281 ≤ 9640 :=
    liftCount (m := 35141) (e := 15) (a := 4955) (by decide) (by decide) (by decide) (by decide) (by decide) h35141
  exact endpointCost_of_parts (j := 35140) (a := 9640) (d := 14148)
    (by decide) h70281 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost35141 : endpointCostOK (35141, 38308, 25928) := by
  have h9578 := base_9578
  have h19155 : oddPrimeCount 19155 ≤ 2655 :=
    liftCount (m := 9578) (e := 13) (a := 1182) (by decide) (by decide) (by decide) (by decide) (by decide) h9578
  have h38309 : oddPrimeCount 38309 ≤ 5391 :=
    liftCount (m := 19155) (e := 14) (a := 2655) (by decide) (by decide) (by decide) (by decide) (by decide) h19155
  have h76617 : oddPrimeCount 76617 ≤ 10498 :=
    liftCount (m := 38309) (e := 15) (a := 5391) (by decide) (by decide) (by decide) (by decide) (by decide) h38309
  exact endpointCost_of_parts (j := 38308) (a := 10498) (d := 15430)
    (by decide) h76617 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost38309 : endpointCostOK (38309, 41241, 28189) := by
  have h5156 := base_5156
  have h10311 : oddPrimeCount 10311 ≤ 1545 :=
    liftCount (m := 5156) (e := 12) (a := 686) (by decide) (by decide) (by decide) (by decide) (by decide) h5156
  have h20621 : oddPrimeCount 20621 ≤ 3131 :=
    liftCount (m := 10311) (e := 13) (a := 1545) (by decide) (by decide) (by decide) (by decide) (by decide) h10311
  have h41242 : oddPrimeCount 41242 ≤ 6076 :=
    liftCount (m := 20621) (e := 14) (a := 3131) (by decide) (by decide) (by decide) (by decide) (by decide) h20621
  have h82483 : oddPrimeCount 82483 ≤ 11574 :=
    liftCount (m := 41242) (e := 15) (a := 6076) (by decide) (by decide) (by decide) (by decide) (by decide) h41242
  exact endpointCost_of_parts (j := 41241) (a := 11574) (d := 16615)
    (by decide) h82483 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost41242 : endpointCostOK (41242, 42541, 29073) := by
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
private theorem endpointCost44834 : endpointCostOK (44834, 46026, 31451) := by
  have h5754 := base_5754
  have h11507 : oddPrimeCount 11507 ≤ 1715 :=
    liftCount (m := 5754) (e := 12) (a := 756) (by decide) (by decide) (by decide) (by decide) (by decide) h5754
  have h23014 : oddPrimeCount 23014 ≤ 3485 :=
    liftCount (m := 11507) (e := 13) (a := 1715) (by decide) (by decide) (by decide) (by decide) (by decide) h11507
  have h46027 : oddPrimeCount 46027 ≤ 6772 :=
    liftCount (m := 23014) (e := 14) (a := 3485) (by decide) (by decide) (by decide) (by decide) (by decide) h23014
  have h92053 : oddPrimeCount 92053 ≤ 12908 :=
    liftCount (m := 46027) (e := 15) (a := 6772) (by decide) (by decide) (by decide) (by decide) (by decide) h46027
  exact endpointCost_of_parts (j := 46026) (a := 12908) (d := 18543)
    (by decide) h92053 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost46027 : endpointCostOK (46027, 47248, 32287) := by
  have h5907 := base_5907
  have h11813 : oddPrimeCount 11813 ≤ 1760 :=
    liftCount (m := 5907) (e := 12) (a := 776) (by decide) (by decide) (by decide) (by decide) (by decide) h5907
  have h23625 : oddPrimeCount 23625 ≤ 3577 :=
    liftCount (m := 11813) (e := 13) (a := 1760) (by decide) (by decide) (by decide) (by decide) (by decide) h11813
  have h47249 : oddPrimeCount 47249 ≤ 6952 :=
    liftCount (m := 23625) (e := 14) (a := 3577) (by decide) (by decide) (by decide) (by decide) (by decide) h23625
  have h94497 : oddPrimeCount 94497 ≤ 13251 :=
    liftCount (m := 47249) (e := 15) (a := 6952) (by decide) (by decide) (by decide) (by decide) (by decide) h47249
  exact endpointCost_of_parts (j := 47248) (a := 13251) (d := 19036)
    (by decide) h94497 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost47249 : endpointCostOK (47249, 48199, 32930) := by
  have h6025 := base_6025
  have h12050 : oddPrimeCount 12050 ≤ 1788 :=
    liftCount (m := 6025) (e := 12) (a := 784) (by decide) (by decide) (by decide) (by decide) (by decide) h6025
  have h24100 : oddPrimeCount 24100 ≤ 3641 :=
    liftCount (m := 12050) (e := 13) (a := 1788) (by decide) (by decide) (by decide) (by decide) (by decide) h12050
  have h48200 : oddPrimeCount 48200 ≤ 7083 :=
    liftCount (m := 24100) (e := 14) (a := 3641) (by decide) (by decide) (by decide) (by decide) (by decide) h24100
  have h96399 : oddPrimeCount 96399 ≤ 13509 :=
    liftCount (m := 48200) (e := 15) (a := 7083) (by decide) (by decide) (by decide) (by decide) (by decide) h48200
  exact endpointCost_of_parts (j := 48199) (a := 13509) (d := 19421)
    (by decide) h96399 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost48200 : endpointCostOK (48200, 49166, 33594) := by
  have h6146 := base_6146
  have h12292 : oddPrimeCount 12292 ≤ 1824 :=
    liftCount (m := 6146) (e := 12) (a := 800) (by decide) (by decide) (by decide) (by decide) (by decide) h6146
  have h24584 : oddPrimeCount 24584 ≤ 3715 :=
    liftCount (m := 12292) (e := 13) (a := 1824) (by decide) (by decide) (by decide) (by decide) (by decide) h12292
  have h49167 : oddPrimeCount 49167 ≤ 7227 :=
    liftCount (m := 24584) (e := 14) (a := 3715) (by decide) (by decide) (by decide) (by decide) (by decide) h24584
  have h98333 : oddPrimeCount 98333 ≤ 13782 :=
    liftCount (m := 49167) (e := 15) (a := 7227) (by decide) (by decide) (by decide) (by decide) (by decide) h49167
  exact endpointCost_of_parts (j := 49166) (a := 13782) (d := 19812)
    (by decide) h98333 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost49167 : endpointCostOK (49167, 50159, 34270) := by
  have h6270 := base_6270
  have h12540 : oddPrimeCount 12540 ≤ 1859 :=
    liftCount (m := 6270) (e := 12) (a := 814) (by decide) (by decide) (by decide) (by decide) (by decide) h6270
  have h25080 : oddPrimeCount 25080 ≤ 3788 :=
    liftCount (m := 12540) (e := 13) (a := 1859) (by decide) (by decide) (by decide) (by decide) (by decide) h12540
  have h50160 : oddPrimeCount 50160 ≤ 7370 :=
    liftCount (m := 25080) (e := 14) (a := 3788) (by decide) (by decide) (by decide) (by decide) (by decide) h25080
  have h100319 : oddPrimeCount 100319 ≤ 14058 :=
    liftCount (m := 50160) (e := 15) (a := 7370) (by decide) (by decide) (by decide) (by decide) (by decide) h50160
  exact endpointCost_of_parts (j := 50159) (a := 14058) (d := 20212)
    (by decide) h100319 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost50160 : endpointCostOK (50160, 51167, 34961) := by
  have h6396 := base_6396
  have h12792 : oddPrimeCount 12792 ≤ 1898 :=
    liftCount (m := 6396) (e := 12) (a := 832) (by decide) (by decide) (by decide) (by decide) (by decide) h6396
  have h25584 : oddPrimeCount 25584 ≤ 3866 :=
    liftCount (m := 12792) (e := 13) (a := 1898) (by decide) (by decide) (by decide) (by decide) (by decide) h12792
  have h51168 : oddPrimeCount 51168 ≤ 7520 :=
    liftCount (m := 25584) (e := 14) (a := 3866) (by decide) (by decide) (by decide) (by decide) (by decide) h25584
  have h102335 : oddPrimeCount 102335 ≤ 14342 :=
    liftCount (m := 51168) (e := 15) (a := 7520) (by decide) (by decide) (by decide) (by decide) (by decide) h51168
  exact endpointCost_of_parts (j := 51167) (a := 14342) (d := 20619)
    (by decide) h102335 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost51168 : endpointCostOK (51168, 52203, 35664) := by
  have h6526 := base_6526
  have h13051 : oddPrimeCount 13051 ≤ 1929 :=
    liftCount (m := 6526) (e := 12) (a := 842) (by decide) (by decide) (by decide) (by decide) (by decide) h6526
  have h26102 : oddPrimeCount 26102 ≤ 3936 :=
    liftCount (m := 13051) (e := 13) (a := 1929) (by decide) (by decide) (by decide) (by decide) (by decide) h13051
  have h52204 : oddPrimeCount 52204 ≤ 7664 :=
    liftCount (m := 26102) (e := 14) (a := 3936) (by decide) (by decide) (by decide) (by decide) (by decide) h26102
  have h104407 : oddPrimeCount 104407 ≤ 14624 :=
    liftCount (m := 52204) (e := 15) (a := 7664) (by decide) (by decide) (by decide) (by decide) (by decide) h52204
  exact endpointCost_of_parts (j := 52203) (a := 14624) (d := 21040)
    (by decide) h104407 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost52204 : endpointCostOK (52204, 53271, 36390) := by
  have h6659 := base_6659
  have h13318 : oddPrimeCount 13318 ≤ 1966 :=
    liftCount (m := 6659) (e := 12) (a := 857) (by decide) (by decide) (by decide) (by decide) (by decide) h6659
  have h26636 : oddPrimeCount 26636 ≤ 4014 :=
    liftCount (m := 13318) (e := 13) (a := 1966) (by decide) (by decide) (by decide) (by decide) (by decide) h13318
  have h53272 : oddPrimeCount 53272 ≤ 7819 :=
    liftCount (m := 26636) (e := 14) (a := 4014) (by decide) (by decide) (by decide) (by decide) (by decide) h26636
  have h106543 : oddPrimeCount 106543 ≤ 14921 :=
    liftCount (m := 53272) (e := 15) (a := 7819) (by decide) (by decide) (by decide) (by decide) (by decide) h53272
  exact endpointCost_of_parts (j := 53271) (a := 14921) (d := 21469)
    (by decide) h106543 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost53272 : endpointCostOK (53272, 54359, 37134) := by
  have h6795 := base_6795
  have h13590 : oddPrimeCount 13590 ≤ 2006 :=
    liftCount (m := 6795) (e := 12) (a := 874) (by decide) (by decide) (by decide) (by decide) (by decide) h6795
  have h27180 : oddPrimeCount 27180 ≤ 4096 :=
    liftCount (m := 13590) (e := 13) (a := 2006) (by decide) (by decide) (by decide) (by decide) (by decide) h13590
  have h54360 : oddPrimeCount 54360 ≤ 7978 :=
    liftCount (m := 27180) (e := 14) (a := 4096) (by decide) (by decide) (by decide) (by decide) (by decide) h27180
  have h108719 : oddPrimeCount 108719 ≤ 15226 :=
    liftCount (m := 54360) (e := 15) (a := 7978) (by decide) (by decide) (by decide) (by decide) (by decide) h54360
  exact endpointCost_of_parts (j := 54359) (a := 15226) (d := 21908)
    (by decide) h108719 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost54360 : endpointCostOK (54360, 55479, 37895) := by
  have h6935 := base_6935
  have h13870 : oddPrimeCount 13870 ≤ 2044 :=
    liftCount (m := 6935) (e := 12) (a := 889) (by decide) (by decide) (by decide) (by decide) (by decide) h6935
  have h27740 : oddPrimeCount 27740 ≤ 4177 :=
    liftCount (m := 13870) (e := 13) (a := 2044) (by decide) (by decide) (by decide) (by decide) (by decide) h13870
  have h55480 : oddPrimeCount 55480 ≤ 8139 :=
    liftCount (m := 27740) (e := 14) (a := 4177) (by decide) (by decide) (by decide) (by decide) (by decide) h27740
  have h110959 : oddPrimeCount 110959 ≤ 15536 :=
    liftCount (m := 55480) (e := 15) (a := 8139) (by decide) (by decide) (by decide) (by decide) (by decide) h55480
  exact endpointCost_of_parts (j := 55479) (a := 15536) (d := 22359)
    (by decide) h110959 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost55480 : endpointCostOK (55480, 56613, 38674) := by
  have h7077 := base_7077
  have h14154 : oddPrimeCount 14154 ≤ 2086 :=
    liftCount (m := 7077) (e := 12) (a := 907) (by decide) (by decide) (by decide) (by decide) (by decide) h7077
  have h28307 : oddPrimeCount 28307 ≤ 4263 :=
    liftCount (m := 14154) (e := 13) (a := 2086) (by decide) (by decide) (by decide) (by decide) (by decide) h14154
  have h56614 : oddPrimeCount 56614 ≤ 8306 :=
    liftCount (m := 28307) (e := 14) (a := 4263) (by decide) (by decide) (by decide) (by decide) (by decide) h28307
  have h113227 : oddPrimeCount 113227 ≤ 15854 :=
    liftCount (m := 56614) (e := 15) (a := 8306) (by decide) (by decide) (by decide) (by decide) (by decide) h56614
  exact endpointCost_of_parts (j := 56613) (a := 15854) (d := 22820)
    (by decide) h113227 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost56614 : endpointCostOK (56614, 57775, 39466) := by
  have h7222 := base_7222
  have h14444 : oddPrimeCount 14444 ≤ 2125 :=
    liftCount (m := 7222) (e := 12) (a := 922) (by decide) (by decide) (by decide) (by decide) (by decide) h7222
  have h28888 : oddPrimeCount 28888 ≤ 4347 :=
    liftCount (m := 14444) (e := 13) (a := 2125) (by decide) (by decide) (by decide) (by decide) (by decide) h14444
  have h57776 : oddPrimeCount 57776 ≤ 8473 :=
    liftCount (m := 28888) (e := 14) (a := 4347) (by decide) (by decide) (by decide) (by decide) (by decide) h28888
  have h115551 : oddPrimeCount 115551 ≤ 16176 :=
    liftCount (m := 57776) (e := 15) (a := 8473) (by decide) (by decide) (by decide) (by decide) (by decide) h57776
  exact endpointCost_of_parts (j := 57775) (a := 16176) (d := 23290)
    (by decide) h115551 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost57776 : endpointCostOK (57776, 58965, 40276) := by
  have h7371 := base_7371
  have h14742 : oddPrimeCount 14742 ≤ 2165 :=
    liftCount (m := 7371) (e := 12) (a := 937) (by decide) (by decide) (by decide) (by decide) (by decide) h7371
  have h29483 : oddPrimeCount 29483 ≤ 4433 :=
    liftCount (m := 14742) (e := 13) (a := 2165) (by decide) (by decide) (by decide) (by decide) (by decide) h14742
  have h58966 : oddPrimeCount 58966 ≤ 8644 :=
    liftCount (m := 29483) (e := 14) (a := 4433) (by decide) (by decide) (by decide) (by decide) (by decide) h29483
  have h117931 : oddPrimeCount 117931 ≤ 16506 :=
    liftCount (m := 58966) (e := 15) (a := 8644) (by decide) (by decide) (by decide) (by decide) (by decide) h58966
  exact endpointCost_of_parts (j := 58965) (a := 16506) (d := 23770)
    (by decide) h117931 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost58966 : endpointCostOK (58966, 60187, 41107) := by
  have h7524 := base_7524
  have h15047 : oddPrimeCount 15047 ≤ 2206 :=
    liftCount (m := 7524) (e := 12) (a := 952) (by decide) (by decide) (by decide) (by decide) (by decide) h7524
  have h30094 : oddPrimeCount 30094 ≤ 4520 :=
    liftCount (m := 15047) (e := 13) (a := 2206) (by decide) (by decide) (by decide) (by decide) (by decide) h15047
  have h60188 : oddPrimeCount 60188 ≤ 8819 :=
    liftCount (m := 30094) (e := 14) (a := 4520) (by decide) (by decide) (by decide) (by decide) (by decide) h30094
  have h120375 : oddPrimeCount 120375 ≤ 16844 :=
    liftCount (m := 60188) (e := 15) (a := 8819) (by decide) (by decide) (by decide) (by decide) (by decide) h60188
  exact endpointCost_of_parts (j := 60187) (a := 16844) (d := 24263)
    (by decide) h120375 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost60188 : endpointCostOK (60188, 61431, 41959) := by
  have h7679 := base_7679
  have h15358 : oddPrimeCount 15358 ≤ 2251 :=
    liftCount (m := 7679) (e := 12) (a := 972) (by decide) (by decide) (by decide) (by decide) (by decide) h7679
  have h30716 : oddPrimeCount 30716 ≤ 4613 :=
    liftCount (m := 15358) (e := 13) (a := 2251) (by decide) (by decide) (by decide) (by decide) (by decide) h15358
  have h61432 : oddPrimeCount 61432 ≤ 9001 :=
    liftCount (m := 30716) (e := 14) (a := 4613) (by decide) (by decide) (by decide) (by decide) (by decide) h30716
  have h122863 : oddPrimeCount 122863 ≤ 17191 :=
    liftCount (m := 61432) (e := 15) (a := 9001) (by decide) (by decide) (by decide) (by decide) (by decide) h61432
  exact endpointCost_of_parts (j := 61431) (a := 17191) (d := 24768)
    (by decide) h122863 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost61432 : endpointCostOK (61432, 62712, 42828) := by
  have h7840 := base_7840
  have h15679 : oddPrimeCount 15679 ≤ 2295 :=
    liftCount (m := 7840) (e := 12) (a := 989) (by decide) (by decide) (by decide) (by decide) (by decide) h7840
  have h31357 : oddPrimeCount 31357 ≤ 4707 :=
    liftCount (m := 15679) (e := 13) (a := 2295) (by decide) (by decide) (by decide) (by decide) (by decide) h15679
  have h62713 : oddPrimeCount 62713 ≤ 9186 :=
    liftCount (m := 31357) (e := 14) (a := 4707) (by decide) (by decide) (by decide) (by decide) (by decide) h31357
  have h125425 : oddPrimeCount 125425 ≤ 17547 :=
    liftCount (m := 62713) (e := 15) (a := 9186) (by decide) (by decide) (by decide) (by decide) (by decide) h62713
  exact endpointCost_of_parts (j := 62712) (a := 17547) (d := 25281)
    (by decide) h125425 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost62713 : endpointCostOK (62713, 64023, 43723) := by
  have h8003 := base_8003
  have h16006 : oddPrimeCount 16006 ≤ 2339 :=
    liftCount (m := 8003) (e := 12) (a := 1006) (by decide) (by decide) (by decide) (by decide) (by decide) h8003
  have h32012 : oddPrimeCount 32012 ≤ 4801 :=
    liftCount (m := 16006) (e := 13) (a := 2339) (by decide) (by decide) (by decide) (by decide) (by decide) h16006
  have h64024 : oddPrimeCount 64024 ≤ 9374 :=
    liftCount (m := 32012) (e := 14) (a := 4801) (by decide) (by decide) (by decide) (by decide) (by decide) h32012
  have h128047 : oddPrimeCount 128047 ≤ 17910 :=
    liftCount (m := 64024) (e := 15) (a := 9374) (by decide) (by decide) (by decide) (by decide) (by decide) h64024
  exact endpointCost_of_parts (j := 64023) (a := 17910) (d := 25813)
    (by decide) h128047 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost64024 : endpointCostOK (64024, 67574, 44966) := by
  have h8447 := base_8447
  have h16894 : oddPrimeCount 16894 ≤ 2355 :=
    liftCount (m := 8447) (e := 13) (a := 1056) (by decide) (by decide) (by decide) (by decide) (by decide) h8447
  have h33788 : oddPrimeCount 33788 ≤ 4768 :=
    liftCount (m := 16894) (e := 14) (a := 2355) (by decide) (by decide) (by decide) (by decide) (by decide) h16894
  have h67575 : oddPrimeCount 67575 ≤ 9273 :=
    liftCount (m := 33788) (e := 15) (a := 4768) (by decide) (by decide) (by decide) (by decide) (by decide) h33788
  have h135149 : oddPrimeCount 135149 ≤ 17719 :=
    liftCount (m := 67575) (e := 16) (a := 9273) (by decide) (by decide) (by decide) (by decide) (by decide) h67575
  exact endpointCost_of_parts (j := 67574) (a := 17719) (d := 27247)
    (by decide) h135149 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost67575 : endpointCostOK (67575, 71339, 47465) := by
  have h8918 := base_8918
  have h17835 : oddPrimeCount 17835 ≤ 2479 :=
    liftCount (m := 8918) (e := 13) (a := 1107) (by decide) (by decide) (by decide) (by decide) (by decide) h8918
  have h35670 : oddPrimeCount 35670 ≤ 5026 :=
    liftCount (m := 17835) (e := 14) (a := 2479) (by decide) (by decide) (by decide) (by decide) (by decide) h17835
  have h71340 : oddPrimeCount 71340 ≤ 9782 :=
    liftCount (m := 35670) (e := 15) (a := 5026) (by decide) (by decide) (by decide) (by decide) (by decide) h35670
  have h142679 : oddPrimeCount 142679 ≤ 18699 :=
    liftCount (m := 71340) (e := 16) (a := 9782) (by decide) (by decide) (by decide) (by decide) (by decide) h71340
  exact endpointCost_of_parts (j := 71339) (a := 18699) (d := 28766)
    (by decide) h142679 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost71340 : endpointCostOK (71340, 75315, 50111) := by
  have h9415 := base_9415
  have h18829 : oddPrimeCount 18829 ≤ 2611 :=
    liftCount (m := 9415) (e := 13) (a := 1163) (by decide) (by decide) (by decide) (by decide) (by decide) h9415
  have h37658 : oddPrimeCount 37658 ≤ 5300 :=
    liftCount (m := 18829) (e := 14) (a := 2611) (by decide) (by decide) (by decide) (by decide) (by decide) h18829
  have h75316 : oddPrimeCount 75316 ≤ 10321 :=
    liftCount (m := 37658) (e := 15) (a := 5300) (by decide) (by decide) (by decide) (by decide) (by decide) h37658
  have h150631 : oddPrimeCount 150631 ≤ 19735 :=
    liftCount (m := 75316) (e := 16) (a := 10321) (by decide) (by decide) (by decide) (by decide) (by decide) h75316
  exact endpointCost_of_parts (j := 75315) (a := 19735) (d := 30376)
    (by decide) h150631 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost75316 : endpointCostOK (75316, 79515, 52905) := by
  have h9940 := base_9940
  have h19879 : oddPrimeCount 19879 ≤ 2753 :=
    liftCount (m := 9940) (e := 13) (a := 1224) (by decide) (by decide) (by decide) (by decide) (by decide) h9940
  have h39758 : oddPrimeCount 39758 ≤ 5592 :=
    liftCount (m := 19879) (e := 14) (a := 2753) (by decide) (by decide) (by decide) (by decide) (by decide) h19879
  have h79516 : oddPrimeCount 79516 ≤ 10893 :=
    liftCount (m := 39758) (e := 15) (a := 5592) (by decide) (by decide) (by decide) (by decide) (by decide) h39758
  have h159031 : oddPrimeCount 159031 ≤ 20832 :=
    liftCount (m := 79516) (e := 16) (a := 10893) (by decide) (by decide) (by decide) (by decide) (by decide) h79516
  exact endpointCost_of_parts (j := 79515) (a := 20832) (d := 32073)
    (by decide) h159031 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost79516 : endpointCostOK (79516, 83407, 55774) := by
  have h5213 := base_5213
  have h10426 : oddPrimeCount 10426 ≤ 1560 :=
    liftCount (m := 5213) (e := 12) (a := 692) (by decide) (by decide) (by decide) (by decide) (by decide) h5213
  have h20852 : oddPrimeCount 20852 ≤ 3164 :=
    liftCount (m := 10426) (e := 13) (a := 1560) (by decide) (by decide) (by decide) (by decide) (by decide) h10426
  have h41704 : oddPrimeCount 41704 ≤ 6142 :=
    liftCount (m := 20852) (e := 14) (a := 3164) (by decide) (by decide) (by decide) (by decide) (by decide) h20852
  have h83408 : oddPrimeCount 83408 ≤ 11702 :=
    liftCount (m := 41704) (e := 15) (a := 6142) (by decide) (by decide) (by decide) (by decide) (by decide) h41704
  have h166815 : oddPrimeCount 166815 ≤ 22128 :=
    liftCount (m := 83408) (e := 16) (a := 11702) (by decide) (by decide) (by decide) (by decide) (by decide) h83408
  exact endpointCost_of_parts (j := 83407) (a := 22128) (d := 33646)
    (by decide) h166815 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost83408 : endpointCostOK (83408, 87502, 58507) := by
  have h5469 := base_5469
  have h10938 : oddPrimeCount 10938 ≤ 1631 :=
    liftCount (m := 5469) (e := 12) (a := 720) (by decide) (by decide) (by decide) (by decide) (by decide) h5469
  have h21876 : oddPrimeCount 21876 ≤ 3313 :=
    liftCount (m := 10938) (e := 13) (a := 1631) (by decide) (by decide) (by decide) (by decide) (by decide) h10938
  have h43752 : oddPrimeCount 43752 ≤ 6438 :=
    liftCount (m := 21876) (e := 14) (a := 3313) (by decide) (by decide) (by decide) (by decide) (by decide) h21876
  have h87503 : oddPrimeCount 87503 ≤ 12271 :=
    liftCount (m := 43752) (e := 15) (a := 6438) (by decide) (by decide) (by decide) (by decide) (by decide) h43752
  have h175005 : oddPrimeCount 175005 ≤ 23208 :=
    liftCount (m := 87503) (e := 16) (a := 12271) (by decide) (by decide) (by decide) (by decide) (by decide) h87503
  exact endpointCost_of_parts (j := 87502) (a := 23208) (d := 35299)
    (by decide) h175005 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost87503 : endpointCostOK (87503, 91798, 61380) := by
  have h5738 := base_5738
  have h11475 : oddPrimeCount 11475 ≤ 1709 :=
    liftCount (m := 5738) (e := 12) (a := 753) (by decide) (by decide) (by decide) (by decide) (by decide) h5738
  have h22950 : oddPrimeCount 22950 ≤ 3474 :=
    liftCount (m := 11475) (e := 13) (a := 1709) (by decide) (by decide) (by decide) (by decide) (by decide) h11475
  have h45900 : oddPrimeCount 45900 ≤ 6752 :=
    liftCount (m := 22950) (e := 14) (a := 3474) (by decide) (by decide) (by decide) (by decide) (by decide) h22950
  have h91799 : oddPrimeCount 91799 ≤ 12872 :=
    liftCount (m := 45900) (e := 15) (a := 6752) (by decide) (by decide) (by decide) (by decide) (by decide) h45900
  have h183597 : oddPrimeCount 183597 ≤ 24346 :=
    liftCount (m := 91799) (e := 16) (a := 12872) (by decide) (by decide) (by decide) (by decide) (by decide) h91799
  exact endpointCost_of_parts (j := 91798) (a := 24346) (d := 37034)
    (by decide) h183597 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost91799 : endpointCostOK (91799, 96318, 64397) := by
  have h6020 := base_6020
  have h12040 : oddPrimeCount 12040 ≤ 1787 :=
    liftCount (m := 6020) (e := 12) (a := 784) (by decide) (by decide) (by decide) (by decide) (by decide) h6020
  have h24080 : oddPrimeCount 24080 ≤ 3639 :=
    liftCount (m := 12040) (e := 13) (a := 1787) (by decide) (by decide) (by decide) (by decide) (by decide) h12040
  have h48160 : oddPrimeCount 48160 ≤ 7079 :=
    liftCount (m := 24080) (e := 14) (a := 3639) (by decide) (by decide) (by decide) (by decide) (by decide) h24080
  have h96319 : oddPrimeCount 96319 ≤ 13500 :=
    liftCount (m := 48160) (e := 15) (a := 7079) (by decide) (by decide) (by decide) (by decide) (by decide) h48160
  have h192637 : oddPrimeCount 192637 ≤ 25539 :=
    liftCount (m := 96319) (e := 16) (a := 13500) (by decide) (by decide) (by decide) (by decide) (by decide) h96319
  exact endpointCost_of_parts (j := 96318) (a := 25539) (d := 38858)
    (by decide) h192637 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost96319 : endpointCostOK (96319, 101051, 67567) := by
  have h6316 := base_6316
  have h12632 : oddPrimeCount 12632 ≤ 1872 :=
    liftCount (m := 6316) (e := 12) (a := 820) (by decide) (by decide) (by decide) (by decide) (by decide) h6316
  have h25263 : oddPrimeCount 25263 ≤ 3815 :=
    liftCount (m := 12632) (e := 13) (a := 1872) (by decide) (by decide) (by decide) (by decide) (by decide) h12632
  have h50526 : oddPrimeCount 50526 ≤ 7424 :=
    liftCount (m := 25263) (e := 14) (a := 3815) (by decide) (by decide) (by decide) (by decide) (by decide) h25263
  have h101052 : oddPrimeCount 101052 ≤ 14160 :=
    liftCount (m := 50526) (e := 15) (a := 7424) (by decide) (by decide) (by decide) (by decide) (by decide) h50526
  have h202103 : oddPrimeCount 202103 ≤ 26791 :=
    liftCount (m := 101052) (e := 16) (a := 14160) (by decide) (by decide) (by decide) (by decide) (by decide) h101052
  exact endpointCost_of_parts (j := 101051) (a := 26791) (d := 40776)
    (by decide) h202103 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost101052 : endpointCostOK (101052, 106038, 70891) := by
  have h6628 := base_6628
  have h13255 : oddPrimeCount 13255 ≤ 1958 :=
    liftCount (m := 6628) (e := 12) (a := 854) (by decide) (by decide) (by decide) (by decide) (by decide) h6628
  have h26510 : oddPrimeCount 26510 ≤ 3997 :=
    liftCount (m := 13255) (e := 13) (a := 1958) (by decide) (by decide) (by decide) (by decide) (by decide) h13255
  have h53020 : oddPrimeCount 53020 ≤ 7784 :=
    liftCount (m := 26510) (e := 14) (a := 3997) (by decide) (by decide) (by decide) (by decide) (by decide) h26510
  have h106039 : oddPrimeCount 106039 ≤ 14853 :=
    liftCount (m := 53020) (e := 15) (a := 7784) (by decide) (by decide) (by decide) (by decide) (by decide) h53020
  have h212077 : oddPrimeCount 212077 ≤ 28107 :=
    liftCount (m := 106039) (e := 16) (a := 14853) (by decide) (by decide) (by decide) (by decide) (by decide) h106039
  exact endpointCost_of_parts (j := 106038) (a := 28107) (d := 42784)
    (by decide) h212077 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost106039 : endpointCostOK (106039, 111271, 74389) := by
  have h6955 := base_6955
  have h13909 : oddPrimeCount 13909 ≤ 2050 :=
    liftCount (m := 6955) (e := 12) (a := 891) (by decide) (by decide) (by decide) (by decide) (by decide) h6955
  have h27818 : oddPrimeCount 27818 ≤ 4189 :=
    liftCount (m := 13909) (e := 13) (a := 2050) (by decide) (by decide) (by decide) (by decide) (by decide) h13909
  have h55636 : oddPrimeCount 55636 ≤ 8163 :=
    liftCount (m := 27818) (e := 14) (a := 4189) (by decide) (by decide) (by decide) (by decide) (by decide) h27818
  have h111272 : oddPrimeCount 111272 ≤ 15581 :=
    liftCount (m := 55636) (e := 15) (a := 8163) (by decide) (by decide) (by decide) (by decide) (by decide) h55636
  have h222543 : oddPrimeCount 222543 ≤ 29490 :=
    liftCount (m := 111272) (e := 16) (a := 15581) (by decide) (by decide) (by decide) (by decide) (by decide) h111272
  exact endpointCost_of_parts (j := 111271) (a := 29490) (d := 44899)
    (by decide) h222543 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost111272 : endpointCostOK (111272, 116761, 78059) := by
  have h7298 := base_7298
  have h14596 : oddPrimeCount 14596 ≤ 2145 :=
    liftCount (m := 7298) (e := 12) (a := 929) (by decide) (by decide) (by decide) (by decide) (by decide) h7298
  have h29191 : oddPrimeCount 29191 ≤ 4390 :=
    liftCount (m := 14596) (e := 13) (a := 2145) (by decide) (by decide) (by decide) (by decide) (by decide) h14596
  have h58381 : oddPrimeCount 58381 ≤ 8560 :=
    liftCount (m := 29191) (e := 14) (a := 4390) (by decide) (by decide) (by decide) (by decide) (by decide) h29191
  have h116762 : oddPrimeCount 116762 ≤ 16344 :=
    liftCount (m := 58381) (e := 15) (a := 8560) (by decide) (by decide) (by decide) (by decide) (by decide) h58381
  have h233523 : oddPrimeCount 233523 ≤ 30939 :=
    liftCount (m := 116762) (e := 16) (a := 16344) (by decide) (by decide) (by decide) (by decide) (by decide) h116762
  exact endpointCost_of_parts (j := 116761) (a := 30939) (d := 47120)
    (by decide) h233523 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost116762 : endpointCostOK (116762, 122530, 81916) := by
  have h7659 := base_7659
  have h15317 : oddPrimeCount 15317 ≤ 2246 :=
    liftCount (m := 7659) (e := 12) (a := 970) (by decide) (by decide) (by decide) (by decide) (by decide) h7659
  have h30633 : oddPrimeCount 30633 ≤ 4602 :=
    liftCount (m := 15317) (e := 13) (a := 2246) (by decide) (by decide) (by decide) (by decide) (by decide) h15317
  have h61266 : oddPrimeCount 61266 ≤ 8978 :=
    liftCount (m := 30633) (e := 14) (a := 4602) (by decide) (by decide) (by decide) (by decide) (by decide) h30633
  have h122531 : oddPrimeCount 122531 ≤ 17146 :=
    liftCount (m := 61266) (e := 15) (a := 8978) (by decide) (by decide) (by decide) (by decide) (by decide) h61266
  have h245061 : oddPrimeCount 245061 ≤ 32462 :=
    liftCount (m := 122531) (e := 16) (a := 17146) (by decide) (by decide) (by decide) (by decide) (by decide) h122531
  exact endpointCost_of_parts (j := 122530) (a := 32462) (d := 49454)
    (by decide) h245061 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost122531 : endpointCostOK (122531, 128599, 85964) := by
  have h8038 := base_8038
  have h16075 : oddPrimeCount 16075 ≤ 2348 :=
    liftCount (m := 8038) (e := 12) (a := 1009) (by decide) (by decide) (by decide) (by decide) (by decide) h8038
  have h32150 : oddPrimeCount 32150 ≤ 4821 :=
    liftCount (m := 16075) (e := 13) (a := 2348) (by decide) (by decide) (by decide) (by decide) (by decide) h16075
  have h64300 : oddPrimeCount 64300 ≤ 9413 :=
    liftCount (m := 32150) (e := 14) (a := 4821) (by decide) (by decide) (by decide) (by decide) (by decide) h32150
  have h128600 : oddPrimeCount 128600 ≤ 17986 :=
    liftCount (m := 64300) (e := 15) (a := 9413) (by decide) (by decide) (by decide) (by decide) (by decide) h64300
  have h257199 : oddPrimeCount 257199 ≤ 34061 :=
    liftCount (m := 128600) (e := 16) (a := 17986) (by decide) (by decide) (by decide) (by decide) (by decide) h128600
  exact endpointCost_of_parts (j := 128599) (a := 34061) (d := 51903)
    (by decide) h257199 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost128600 : endpointCostOK (128600, 139288, 90869) := by
  have h8706 := base_8706
  have h17412 : oddPrimeCount 17412 ≤ 2422 :=
    liftCount (m := 8706) (e := 13) (a := 1083) (by decide) (by decide) (by decide) (by decide) (by decide) h8706
  have h34823 : oddPrimeCount 34823 ≤ 4909 :=
    liftCount (m := 17412) (e := 14) (a := 2422) (by decide) (by decide) (by decide) (by decide) (by decide) h17412
  have h69645 : oddPrimeCount 69645 ≤ 9552 :=
    liftCount (m := 34823) (e := 15) (a := 4909) (by decide) (by decide) (by decide) (by decide) (by decide) h34823
  have h139289 : oddPrimeCount 139289 ≤ 18257 :=
    liftCount (m := 69645) (e := 16) (a := 9552) (by decide) (by decide) (by decide) (by decide) (by decide) h69645
  have h278577 : oddPrimeCount 278577 ≤ 34643 :=
    liftCount (m := 139289) (e := 17) (a := 18257) (by decide) (by decide) (by decide) (by decide) (by decide) h139289
  exact endpointCost_of_parts (j := 139288) (a := 34643) (d := 56226)
    (by decide) h278577 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost139289 : endpointCostOK (139289, 150873, 98423) := by
  have h9430 := base_9430
  have h18860 : oddPrimeCount 18860 ≤ 2615 :=
    liftCount (m := 9430) (e := 13) (a := 1165) (by decide) (by decide) (by decide) (by decide) (by decide) h9430
  have h37719 : oddPrimeCount 37719 ≤ 5309 :=
    liftCount (m := 18860) (e := 14) (a := 2615) (by decide) (by decide) (by decide) (by decide) (by decide) h18860
  have h75437 : oddPrimeCount 75437 ≤ 10338 :=
    liftCount (m := 37719) (e := 15) (a := 5309) (by decide) (by decide) (by decide) (by decide) (by decide) h37719
  have h150874 : oddPrimeCount 150874 ≤ 19767 :=
    liftCount (m := 75437) (e := 16) (a := 10338) (by decide) (by decide) (by decide) (by decide) (by decide) h75437
  have h301747 : oddPrimeCount 301747 ≤ 37516 :=
    liftCount (m := 150874) (e := 17) (a := 19767) (by decide) (by decide) (by decide) (by decide) (by decide) h150874
  exact endpointCost_of_parts (j := 150873) (a := 37516) (d := 60907)
    (by decide) h301747 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost150874 : endpointCostOK (150874, 162886, 106531) := by
  have h5091 := base_5091
  have h10181 : oddPrimeCount 10181 ≤ 1527 :=
    liftCount (m := 5091) (e := 12) (a := 679) (by decide) (by decide) (by decide) (by decide) (by decide) h5091
  have h20361 : oddPrimeCount 20361 ≤ 3093 :=
    liftCount (m := 10181) (e := 13) (a := 1527) (by decide) (by decide) (by decide) (by decide) (by decide) h10181
  have h40722 : oddPrimeCount 40722 ≤ 6001 :=
    liftCount (m := 20361) (e := 14) (a := 3093) (by decide) (by decide) (by decide) (by decide) (by decide) h20361
  have h81444 : oddPrimeCount 81444 ≤ 11430 :=
    liftCount (m := 40722) (e := 15) (a := 6001) (by decide) (by decide) (by decide) (by decide) (by decide) h40722
  have h162887 : oddPrimeCount 162887 ≤ 21610 :=
    liftCount (m := 81444) (e := 16) (a := 11430) (by decide) (by decide) (by decide) (by decide) (by decide) h81444
  have h325773 : oddPrimeCount 325773 ≤ 40773 :=
    liftCount (m := 162887) (e := 17) (a := 21610) (by decide) (by decide) (by decide) (by decide) (by decide) h162887
  exact endpointCost_of_parts (j := 162886) (a := 40773) (d := 65758)
    (by decide) h325773 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost162887 : endpointCostOK (162887, 175856, 115014) := by
  have h5496 := base_5496
  have h10992 : oddPrimeCount 10992 ≤ 1640 :=
    liftCount (m := 5496) (e := 12) (a := 724) (by decide) (by decide) (by decide) (by decide) (by decide) h5496
  have h21983 : oddPrimeCount 21983 ≤ 3331 :=
    liftCount (m := 10992) (e := 13) (a := 1640) (by decide) (by decide) (by decide) (by decide) (by decide) h10992
  have h43965 : oddPrimeCount 43965 ≤ 6471 :=
    liftCount (m := 21983) (e := 14) (a := 3331) (by decide) (by decide) (by decide) (by decide) (by decide) h21983
  have h87929 : oddPrimeCount 87929 ≤ 12333 :=
    liftCount (m := 43965) (e := 15) (a := 6471) (by decide) (by decide) (by decide) (by decide) (by decide) h43965
  have h175857 : oddPrimeCount 175857 ≤ 23324 :=
    liftCount (m := 87929) (e := 16) (a := 12333) (by decide) (by decide) (by decide) (by decide) (by decide) h87929
  have h351713 : oddPrimeCount 351713 ≤ 44013 :=
    liftCount (m := 175857) (e := 17) (a := 23324) (by decide) (by decide) (by decide) (by decide) (by decide) h175857
  exact endpointCost_of_parts (j := 175856) (a := 44013) (d := 71001)
    (by decide) h351713 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost175857 : endpointCostOK (175857, 189863, 124175) := by
  have h5934 := base_5934
  have h11867 : oddPrimeCount 11867 ≤ 1767 :=
    liftCount (m := 5934) (e := 12) (a := 778) (by decide) (by decide) (by decide) (by decide) (by decide) h5934
  have h23733 : oddPrimeCount 23733 ≤ 3592 :=
    liftCount (m := 11867) (e := 13) (a := 1767) (by decide) (by decide) (by decide) (by decide) (by decide) h11867
  have h47466 : oddPrimeCount 47466 ≤ 6982 :=
    liftCount (m := 23733) (e := 14) (a := 3592) (by decide) (by decide) (by decide) (by decide) (by decide) h23733
  have h94932 : oddPrimeCount 94932 ≤ 13310 :=
    liftCount (m := 47466) (e := 15) (a := 6982) (by decide) (by decide) (by decide) (by decide) (by decide) h47466
  have h189864 : oddPrimeCount 189864 ≤ 25176 :=
    liftCount (m := 94932) (e := 16) (a := 13310) (by decide) (by decide) (by decide) (by decide) (by decide) h94932
  have h379727 : oddPrimeCount 379727 ≤ 47512 :=
    liftCount (m := 189864) (e := 17) (a := 25176) (by decide) (by decide) (by decide) (by decide) (by decide) h189864
  exact endpointCost_of_parts (j := 189863) (a := 47512) (d := 76663)
    (by decide) h379727 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost189864 : endpointCostOK (189864, 204988, 134067) := by
  have h6406 := base_6406
  have h12812 : oddPrimeCount 12812 ≤ 1900 :=
    liftCount (m := 6406) (e := 12) (a := 833) (by decide) (by decide) (by decide) (by decide) (by decide) h6406
  have h25624 : oddPrimeCount 25624 ≤ 3871 :=
    liftCount (m := 12812) (e := 13) (a := 1900) (by decide) (by decide) (by decide) (by decide) (by decide) h12812
  have h51248 : oddPrimeCount 51248 ≤ 7531 :=
    liftCount (m := 25624) (e := 14) (a := 3871) (by decide) (by decide) (by decide) (by decide) (by decide) h25624
  have h102495 : oddPrimeCount 102495 ≤ 14364 :=
    liftCount (m := 51248) (e := 15) (a := 7531) (by decide) (by decide) (by decide) (by decide) (by decide) h51248
  have h204989 : oddPrimeCount 204989 ≤ 27175 :=
    liftCount (m := 102495) (e := 16) (a := 14364) (by decide) (by decide) (by decide) (by decide) (by decide) h102495
  have h409977 : oddPrimeCount 409977 ≤ 51291 :=
    liftCount (m := 204989) (e := 17) (a := 27175) (by decide) (by decide) (by decide) (by decide) (by decide) h204989
  exact endpointCost_of_parts (j := 204988) (a := 51291) (d := 82776)
    (by decide) h409977 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost204989 : endpointCostOK (204989, 221323, 144749) := by
  have h6917 := base_6917
  have h13833 : oddPrimeCount 13833 ≤ 2041 :=
    liftCount (m := 6917) (e := 12) (a := 889) (by decide) (by decide) (by decide) (by decide) (by decide) h6917
  have h27666 : oddPrimeCount 27666 ≤ 4169 :=
    liftCount (m := 13833) (e := 13) (a := 2041) (by decide) (by decide) (by decide) (by decide) (by decide) h13833
  have h55331 : oddPrimeCount 55331 ≤ 8121 :=
    liftCount (m := 27666) (e := 14) (a := 4169) (by decide) (by decide) (by decide) (by decide) (by decide) h27666
  have h110662 : oddPrimeCount 110662 ≤ 15498 :=
    liftCount (m := 55331) (e := 15) (a := 8121) (by decide) (by decide) (by decide) (by decide) (by decide) h55331
  have h221324 : oddPrimeCount 221324 ≤ 29330 :=
    liftCount (m := 110662) (e := 16) (a := 15498) (by decide) (by decide) (by decide) (by decide) (by decide) h110662
  have h442647 : oddPrimeCount 442647 ≤ 55368 :=
    liftCount (m := 221324) (e := 17) (a := 29330) (by decide) (by decide) (by decide) (by decide) (by decide) h221324
  exact endpointCost_of_parts (j := 221323) (a := 55368) (d := 89381)
    (by decide) h442647 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost221324 : endpointCostOK (221324, 238981, 156288) := by
  have h7469 := base_7469
  have h14937 : oddPrimeCount 14937 ≤ 2188 :=
    liftCount (m := 7469) (e := 12) (a := 944) (by decide) (by decide) (by decide) (by decide) (by decide) h7469
  have h29873 : oddPrimeCount 29873 ≤ 4486 :=
    liftCount (m := 14937) (e := 13) (a := 2188) (by decide) (by decide) (by decide) (by decide) (by decide) h14937
  have h59746 : oddPrimeCount 59746 ≤ 8753 :=
    liftCount (m := 29873) (e := 14) (a := 4486) (by decide) (by decide) (by decide) (by decide) (by decide) h29873
  have h119491 : oddPrimeCount 119491 ≤ 16719 :=
    liftCount (m := 59746) (e := 15) (a := 8753) (by decide) (by decide) (by decide) (by decide) (by decide) h59746
  have h238982 : oddPrimeCount 238982 ≤ 31655 :=
    liftCount (m := 119491) (e := 16) (a := 16719) (by decide) (by decide) (by decide) (by decide) (by decide) h119491
  have h477963 : oddPrimeCount 477963 ≤ 59770 :=
    liftCount (m := 238982) (e := 17) (a := 31655) (by decide) (by decide) (by decide) (by decide) (by decide) h238982
  exact endpointCost_of_parts (j := 238981) (a := 59770) (d := 96518)
    (by decide) h477963 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost238982 : endpointCostOK (238982, 265720, 169903) := by
  have h8304 := base_8304
  have h16608 : oddPrimeCount 16608 ≤ 2318 :=
    liftCount (m := 8304) (e := 13) (a := 1041) (by decide) (by decide) (by decide) (by decide) (by decide) h8304
  have h33216 : oddPrimeCount 33216 ≤ 4690 :=
    liftCount (m := 16608) (e := 14) (a := 2318) (by decide) (by decide) (by decide) (by decide) (by decide) h16608
  have h66431 : oddPrimeCount 66431 ≤ 9118 :=
    liftCount (m := 33216) (e := 15) (a := 4690) (by decide) (by decide) (by decide) (by decide) (by decide) h33216
  have h132861 : oddPrimeCount 132861 ≤ 17421 :=
    liftCount (m := 66431) (e := 16) (a := 9118) (by decide) (by decide) (by decide) (by decide) (by decide) h66431
  have h265721 : oddPrimeCount 265721 ≤ 33051 :=
    liftCount (m := 132861) (e := 17) (a := 17421) (by decide) (by decide) (by decide) (by decide) (by decide) h132861
  have h531441 : oddPrimeCount 531441 ≤ 62575 :=
    liftCount (m := 265721) (e := 18) (a := 33051) (by decide) (by decide) (by decide) (by decide) (by decide) h265721
  exact endpointCost_of_parts (j := 265720) (a := 62575) (d := 107328)
    (by decide) h531441 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost265721 : endpointCostOK (265721, 295469, 188916) := by
  have h9234 := base_9234
  have h18467 : oddPrimeCount 18467 ≤ 2563 :=
    liftCount (m := 9234) (e := 13) (a := 1143) (by decide) (by decide) (by decide) (by decide) (by decide) h9234
  have h36934 : oddPrimeCount 36934 ≤ 5201 :=
    liftCount (m := 18467) (e := 14) (a := 2563) (by decide) (by decide) (by decide) (by decide) (by decide) h18467
  have h73868 : oddPrimeCount 73868 ≤ 10125 :=
    liftCount (m := 36934) (e := 15) (a := 5201) (by decide) (by decide) (by decide) (by decide) (by decide) h36934
  have h147735 : oddPrimeCount 147735 ≤ 19358 :=
    liftCount (m := 73868) (e := 16) (a := 10125) (by decide) (by decide) (by decide) (by decide) (by decide) h73868
  have h295470 : oddPrimeCount 295470 ≤ 36738 :=
    liftCount (m := 147735) (e := 17) (a := 19358) (by decide) (by decide) (by decide) (by decide) (by decide) h147735
  have h590939 : oddPrimeCount 590939 ≤ 69568 :=
    liftCount (m := 295470) (e := 18) (a := 36738) (by decide) (by decide) (by decide) (by decide) (by decide) h295470
  exact endpointCost_of_parts (j := 295469) (a := 69568) (d := 119348)
    (by decide) h590939 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost295470 : endpointCostOK (295470, 327979, 209985) := by
  have h5125 := base_5125
  have h10250 : oddPrimeCount 10250 ≤ 1538 :=
    liftCount (m := 5125) (e := 12) (a := 684) (by decide) (by decide) (by decide) (by decide) (by decide) h5125
  have h20499 : oddPrimeCount 20499 ≤ 3114 :=
    liftCount (m := 10250) (e := 13) (a := 1538) (by decide) (by decide) (by decide) (by decide) (by decide) h10250
  have h40998 : oddPrimeCount 40998 ≤ 6042 :=
    liftCount (m := 20499) (e := 14) (a := 3114) (by decide) (by decide) (by decide) (by decide) (by decide) h20499
  have h81995 : oddPrimeCount 81995 ≤ 11508 :=
    liftCount (m := 40998) (e := 15) (a := 6042) (by decide) (by decide) (by decide) (by decide) (by decide) h40998
  have h163990 : oddPrimeCount 163990 ≤ 21757 :=
    liftCount (m := 81995) (e := 16) (a := 11508) (by decide) (by decide) (by decide) (by decide) (by decide) h81995
  have h327980 : oddPrimeCount 327980 ≤ 41049 :=
    liftCount (m := 163990) (e := 17) (a := 21757) (by decide) (by decide) (by decide) (by decide) (by decide) h163990
  have h655959 : oddPrimeCount 655959 ≤ 77491 :=
    liftCount (m := 327980) (e := 18) (a := 41049) (by decide) (by decide) (by decide) (by decide) (by decide) h327980
  exact endpointCost_of_parts (j := 327979) (a := 77491) (d := 132494)
    (by decide) h655959 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost327980 : endpointCostOK (327980, 364067, 233090) := by
  have h5689 := base_5689
  have h11378 : oddPrimeCount 11378 ≤ 1696 :=
    liftCount (m := 5689) (e := 12) (a := 748) (by decide) (by decide) (by decide) (by decide) (by decide) h5689
  have h22755 : oddPrimeCount 22755 ≤ 3446 :=
    liftCount (m := 11378) (e := 13) (a := 1696) (by decide) (by decide) (by decide) (by decide) (by decide) h11378
  have h45509 : oddPrimeCount 45509 ≤ 6696 :=
    liftCount (m := 22755) (e := 14) (a := 3446) (by decide) (by decide) (by decide) (by decide) (by decide) h22755
  have h91017 : oddPrimeCount 91017 ≤ 12763 :=
    liftCount (m := 45509) (e := 15) (a := 6696) (by decide) (by decide) (by decide) (by decide) (by decide) h45509
  have h182034 : oddPrimeCount 182034 ≤ 24140 :=
    liftCount (m := 91017) (e := 16) (a := 12763) (by decide) (by decide) (by decide) (by decide) (by decide) h91017
  have h364068 : oddPrimeCount 364068 ≤ 45555 :=
    liftCount (m := 182034) (e := 17) (a := 24140) (by decide) (by decide) (by decide) (by decide) (by decide) h182034
  have h728135 : oddPrimeCount 728135 ≤ 86007 :=
    liftCount (m := 364068) (e := 18) (a := 45555) (by decide) (by decide) (by decide) (by decide) (by decide) h364068
  exact endpointCost_of_parts (j := 364067) (a := 86007) (d := 147083)
    (by decide) h728135 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost364068 : endpointCostOK (364068, 404108, 258737) := by
  have h6315 := base_6315
  have h12629 : oddPrimeCount 12629 ≤ 1872 :=
    liftCount (m := 6315) (e := 12) (a := 820) (by decide) (by decide) (by decide) (by decide) (by decide) h6315
  have h25257 : oddPrimeCount 25257 ≤ 3814 :=
    liftCount (m := 12629) (e := 13) (a := 1872) (by decide) (by decide) (by decide) (by decide) (by decide) h12629
  have h50514 : oddPrimeCount 50514 ≤ 7422 :=
    liftCount (m := 25257) (e := 14) (a := 3814) (by decide) (by decide) (by decide) (by decide) (by decide) h25257
  have h101028 : oddPrimeCount 101028 ≤ 14157 :=
    liftCount (m := 50514) (e := 15) (a := 7422) (by decide) (by decide) (by decide) (by decide) (by decide) h50514
  have h202055 : oddPrimeCount 202055 ≤ 26785 :=
    liftCount (m := 101028) (e := 16) (a := 14157) (by decide) (by decide) (by decide) (by decide) (by decide) h101028
  have h404109 : oddPrimeCount 404109 ≤ 50556 :=
    liftCount (m := 202055) (e := 17) (a := 26785) (by decide) (by decide) (by decide) (by decide) (by decide) h202055
  have h808217 : oddPrimeCount 808217 ≤ 95457 :=
    liftCount (m := 404109) (e := 18) (a := 50556) (by decide) (by decide) (by decide) (by decide) (by decide) h404109
  exact endpointCost_of_parts (j := 404108) (a := 95457) (d := 163280)
    (by decide) h808217 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost404109 : endpointCostOK (404109, 448564, 287197) := by
  have h7009 := base_7009
  have h14018 : oddPrimeCount 14018 ≤ 2068 :=
    liftCount (m := 7009) (e := 12) (a := 900) (by decide) (by decide) (by decide) (by decide) (by decide) h7009
  have h28036 : oddPrimeCount 28036 ≤ 4224 :=
    liftCount (m := 14018) (e := 13) (a := 2068) (by decide) (by decide) (by decide) (by decide) (by decide) h14018
  have h56071 : oddPrimeCount 56071 ≤ 8229 :=
    liftCount (m := 28036) (e := 14) (a := 4224) (by decide) (by decide) (by decide) (by decide) (by decide) h28036
  have h112142 : oddPrimeCount 112142 ≤ 15705 :=
    liftCount (m := 56071) (e := 15) (a := 8229) (by decide) (by decide) (by decide) (by decide) (by decide) h56071
  have h224283 : oddPrimeCount 224283 ≤ 29722 :=
    liftCount (m := 112142) (e := 16) (a := 15705) (by decide) (by decide) (by decide) (by decide) (by decide) h112142
  have h448565 : oddPrimeCount 448565 ≤ 56108 :=
    liftCount (m := 224283) (e := 17) (a := 29722) (by decide) (by decide) (by decide) (by decide) (by decide) h224283
  have h897129 : oddPrimeCount 897129 ≤ 105948 :=
    liftCount (m := 448565) (e := 18) (a := 56108) (by decide) (by decide) (by decide) (by decide) (by decide) h448565
  exact endpointCost_of_parts (j := 448564) (a := 105948) (d := 181249)
    (by decide) h897129 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost448565 : endpointCostOK (448565, 497933, 318796) := by
  have h7781 := base_7781
  have h15561 : oddPrimeCount 15561 ≤ 2280 :=
    liftCount (m := 7781) (e := 12) (a := 984) (by decide) (by decide) (by decide) (by decide) (by decide) h7781
  have h31121 : oddPrimeCount 31121 ≤ 4674 :=
    liftCount (m := 15561) (e := 13) (a := 2280) (by decide) (by decide) (by decide) (by decide) (by decide) h15561
  have h62242 : oddPrimeCount 62242 ≤ 9119 :=
    liftCount (m := 31121) (e := 14) (a := 4674) (by decide) (by decide) (by decide) (by decide) (by decide) h31121
  have h124484 : oddPrimeCount 124484 ≤ 17417 :=
    liftCount (m := 62242) (e := 15) (a := 9119) (by decide) (by decide) (by decide) (by decide) (by decide) h62242
  have h248967 : oddPrimeCount 248967 ≤ 32977 :=
    liftCount (m := 124484) (e := 16) (a := 17417) (by decide) (by decide) (by decide) (by decide) (by decide) h124484
  have h497934 : oddPrimeCount 497934 ≤ 62267 :=
    liftCount (m := 248967) (e := 17) (a := 32977) (by decide) (by decide) (by decide) (by decide) (by decide) h248967
  have h995867 : oddPrimeCount 995867 ≤ 117593 :=
    liftCount (m := 497934) (e := 18) (a := 62267) (by decide) (by decide) (by decide) (by decide) (by decide) h497934
  exact endpointCost_of_parts (j := 497933) (a := 117593) (d := 201203)
    (by decide) h995867 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost497934 : endpointCostOK (497934, 567913, 356149) := by
  have h8874 := base_8874
  have h17748 : oddPrimeCount 17748 ≤ 2470 :=
    liftCount (m := 8874) (e := 13) (a := 1105) (by decide) (by decide) (by decide) (by decide) (by decide) h8874
  have h35495 : oddPrimeCount 35495 ≤ 5005 :=
    liftCount (m := 17748) (e := 14) (a := 2470) (by decide) (by decide) (by decide) (by decide) (by decide) h17748
  have h70990 : oddPrimeCount 70990 ≤ 9737 :=
    liftCount (m := 35495) (e := 15) (a := 5005) (by decide) (by decide) (by decide) (by decide) (by decide) h35495
  have h141979 : oddPrimeCount 141979 ≤ 18610 :=
    liftCount (m := 70990) (e := 16) (a := 9737) (by decide) (by decide) (by decide) (by decide) (by decide) h70990
  have h283957 : oddPrimeCount 283957 ≤ 35313 :=
    liftCount (m := 141979) (e := 17) (a := 18610) (by decide) (by decide) (by decide) (by decide) (by decide) h141979
  have h567914 : oddPrimeCount 567914 ≤ 66863 :=
    liftCount (m := 283957) (e := 18) (a := 35313) (by decide) (by decide) (by decide) (by decide) (by decide) h283957
  have h1135827 : oddPrimeCount 1135827 ≤ 126643 :=
    liftCount (m := 567914) (e := 19) (a := 66863) (by decide) (by decide) (by decide) (by decide) (by decide) h567914
  exact endpointCost_of_parts (j := 567913) (a := 126643) (d := 229506)
    (by decide) h1135827 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost567914 : endpointCostOK (567914, 647169, 406122) := by
  have h5057 := base_5057
  have h10113 : oddPrimeCount 10113 ≤ 1517 :=
    liftCount (m := 5057) (e := 12) (a := 675) (by decide) (by decide) (by decide) (by decide) (by decide) h5057
  have h20225 : oddPrimeCount 20225 ≤ 3072 :=
    liftCount (m := 10113) (e := 13) (a := 1517) (by decide) (by decide) (by decide) (by decide) (by decide) h10113
  have h40449 : oddPrimeCount 40449 ≤ 5961 :=
    liftCount (m := 20225) (e := 14) (a := 3072) (by decide) (by decide) (by decide) (by decide) (by decide) h20225
  have h80897 : oddPrimeCount 80897 ≤ 11354 :=
    liftCount (m := 40449) (e := 15) (a := 5961) (by decide) (by decide) (by decide) (by decide) (by decide) h40449
  have h161793 : oddPrimeCount 161793 ≤ 21466 :=
    liftCount (m := 80897) (e := 16) (a := 11354) (by decide) (by decide) (by decide) (by decide) (by decide) h80897
  have h323585 : oddPrimeCount 323585 ≤ 40500 :=
    liftCount (m := 161793) (e := 17) (a := 21466) (by decide) (by decide) (by decide) (by decide) (by decide) h161793
  have h647170 : oddPrimeCount 647170 ≤ 76453 :=
    liftCount (m := 323585) (e := 18) (a := 40500) (by decide) (by decide) (by decide) (by decide) (by decide) h323585
  have h1294339 : oddPrimeCount 1294339 ≤ 144576 :=
    liftCount (m := 647170) (e := 19) (a := 76453) (by decide) (by decide) (by decide) (by decide) (by decide) h647170
  exact endpointCost_of_parts (j := 647169) (a := 144576) (d := 261546)
    (by decide) h1294339 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost647170 : endpointCostOK (647170, 737464, 462796) := by
  have h5762 := base_5762
  have h11523 : oddPrimeCount 11523 ≤ 1716 :=
    liftCount (m := 5762) (e := 12) (a := 756) (by decide) (by decide) (by decide) (by decide) (by decide) h5762
  have h23046 : oddPrimeCount 23046 ≤ 3488 :=
    liftCount (m := 11523) (e := 13) (a := 1716) (by decide) (by decide) (by decide) (by decide) (by decide) h11523
  have h46092 : oddPrimeCount 46092 ≤ 6780 :=
    liftCount (m := 23046) (e := 14) (a := 3488) (by decide) (by decide) (by decide) (by decide) (by decide) h23046
  have h92184 : oddPrimeCount 92184 ≤ 12925 :=
    liftCount (m := 46092) (e := 15) (a := 6780) (by decide) (by decide) (by decide) (by decide) (by decide) h46092
  have h184367 : oddPrimeCount 184367 ≤ 24448 :=
    liftCount (m := 92184) (e := 16) (a := 12925) (by decide) (by decide) (by decide) (by decide) (by decide) h92184
  have h368733 : oddPrimeCount 368733 ≤ 46138 :=
    liftCount (m := 184367) (e := 17) (a := 24448) (by decide) (by decide) (by decide) (by decide) (by decide) h184367
  have h737465 : oddPrimeCount 737465 ≤ 87108 :=
    liftCount (m := 368733) (e := 18) (a := 46138) (by decide) (by decide) (by decide) (by decide) (by decide) h368733
  have h1474929 : oddPrimeCount 1474929 ≤ 164735 :=
    liftCount (m := 737465) (e := 19) (a := 87108) (by decide) (by decide) (by decide) (by decide) (by decide) h737465
  exact endpointCost_of_parts (j := 737464) (a := 164735) (d := 298061)
    (by decide) h1474929 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost737465 : endpointCostOK (737465, 808306, 507256) := by
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
private theorem endpointCost808307 : endpointCostOK (808307, 879578, 551992) := by
  have h6872 := base_6872
  have h13744 : oddPrimeCount 13744 ≤ 2029 :=
    liftCount (m := 6872) (e := 12) (a := 884) (by decide) (by decide) (by decide) (by decide) (by decide) h6872
  have h27487 : oddPrimeCount 27487 ≤ 4143 :=
    liftCount (m := 13744) (e := 13) (a := 2029) (by decide) (by decide) (by decide) (by decide) (by decide) h13744
  have h54974 : oddPrimeCount 54974 ≤ 8069 :=
    liftCount (m := 27487) (e := 14) (a := 4143) (by decide) (by decide) (by decide) (by decide) (by decide) h27487
  have h109948 : oddPrimeCount 109948 ≤ 15398 :=
    liftCount (m := 54974) (e := 15) (a := 8069) (by decide) (by decide) (by decide) (by decide) (by decide) h54974
  have h219895 : oddPrimeCount 219895 ≤ 29141 :=
    liftCount (m := 109948) (e := 16) (a := 15398) (by decide) (by decide) (by decide) (by decide) (by decide) h109948
  have h439790 : oddPrimeCount 439790 ≤ 55011 :=
    liftCount (m := 219895) (e := 17) (a := 29141) (by decide) (by decide) (by decide) (by decide) (by decide) h219895
  have h879579 : oddPrimeCount 879579 ≤ 103876 :=
    liftCount (m := 439790) (e := 18) (a := 55011) (by decide) (by decide) (by decide) (by decide) (by decide) h439790
  have h1759157 : oddPrimeCount 1759157 ≤ 196463 :=
    liftCount (m := 879579) (e := 19) (a := 103876) (by decide) (by decide) (by decide) (by decide) (by decide) h879579
  exact endpointCost_of_parts (j := 879578) (a := 196463) (d := 355529)
    (by decide) h1759157 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost879579 : endpointCostOK (879579, 949517, 595873) := by
  have h7419 := base_7419
  have h14837 : oddPrimeCount 14837 ≤ 2176 :=
    liftCount (m := 7419) (e := 12) (a := 940) (by decide) (by decide) (by decide) (by decide) (by decide) h7419
  have h29673 : oddPrimeCount 29673 ≤ 4458 :=
    liftCount (m := 14837) (e := 13) (a := 2176) (by decide) (by decide) (by decide) (by decide) (by decide) h14837
  have h59345 : oddPrimeCount 59345 ≤ 8697 :=
    liftCount (m := 29673) (e := 14) (a := 4458) (by decide) (by decide) (by decide) (by decide) (by decide) h29673
  have h118690 : oddPrimeCount 118690 ≤ 16609 :=
    liftCount (m := 59345) (e := 15) (a := 8697) (by decide) (by decide) (by decide) (by decide) (by decide) h59345
  have h237380 : oddPrimeCount 237380 ≤ 31445 :=
    liftCount (m := 118690) (e := 16) (a := 16609) (by decide) (by decide) (by decide) (by decide) (by decide) h118690
  have h474759 : oddPrimeCount 474759 ≤ 59372 :=
    liftCount (m := 237380) (e := 17) (a := 31445) (by decide) (by decide) (by decide) (by decide) (by decide) h237380
  have h949518 : oddPrimeCount 949518 ≤ 112123 :=
    liftCount (m := 474759) (e := 18) (a := 59372) (by decide) (by decide) (by decide) (by decide) (by decide) h474759
  have h1899035 : oddPrimeCount 1899035 ≤ 212072 :=
    liftCount (m := 949518) (e := 19) (a := 112123) (by decide) (by decide) (by decide) (by decide) (by decide) h949518
  exact endpointCost_of_parts (j := 949517) (a := 212072) (d := 383801)
    (by decide) h1899035 (by decide +kernel) (by decide)

set_option maxRecDepth 20000 in
private theorem endpointCost949518 : endpointCostOK (949518, 1000000, 627559) := by
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
  refine List.forall_mem_cons.mpr ⟨endpointCost306, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost311, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost320, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost329, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost338, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost347, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost360, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost374, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost392, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost413, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost432, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost455, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost483, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost515, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost548, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost590, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost639, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost702, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost848, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost939, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1053, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1188, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1353, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1559, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost1808, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost2115, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost2502, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost2809, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost3173, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost3610, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost4148, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost4797, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5013, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5243, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5489, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost5748, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost6035, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost6336, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost6669, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost7019, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost7410, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost7828, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost8495, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost9238, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost10000, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost10354, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost10728, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost11115, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost11520, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost11946, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost12398, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost12863, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost13357, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost13877, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost14423, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost15010, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost15620, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost16799, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost18080, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost19464, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost20439, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost21480, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost22581, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost23742, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost24968, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost26263, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost27635, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost29080, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost30617, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost32243, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost35141, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost38309, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost41242, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost42542, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost43672, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost44834, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost46027, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost47249, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost48200, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost49167, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost50160, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost51168, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost52204, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost53272, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost54360, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost55480, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost56614, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost57776, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost58966, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost60188, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost61432, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost62713, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost64024, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost67575, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost71340, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost75316, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost79516, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost83408, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost87503, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost91799, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost96319, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost101052, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost106039, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost111272, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost116762, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost122531, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost128600, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost139289, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost150874, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost162887, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost175857, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost189864, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost204989, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost221324, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost238982, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost265721, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost295470, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost327980, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost364068, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost404109, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost448565, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost497934, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost567914, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost647170, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost737465, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost808307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost879579, ?_⟩
  refine List.forall_mem_cons.mpr ⟨endpointCost949518, ?_⟩
  simp

private def smallPrimes : Finset ℕ := {3,5,7,11,13,17}

private def initialError (r : ℕ) : ℚ := if r = 0 then 0 else (2:ℚ)^(r-1)

private def refund (J : ℕ) (A : Finset ℕ) : ℕ := ∑ p ∈ A, (2*J/(p^2)+1)

private def profileChecks (lo hi : ℕ) (c : ℤ) : Prop :=
  ∀ A ∈ smallPrimes.powerset, ∀ t : Fin 5,
    (∏ p ∈ A,p)*19^t.val ≤ 2*hi+2 →
      (c:ℚ) - (refund hi A:ℚ) + (1 + initialError (A.card+t.val)) <
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
    (c - (refund hi A : ℤ) + (1 + (wholeError (A.card+m) : ℤ))) * (D : ℤ) * (19 : ℤ)^m <
      (lo : ℤ) * (P : ℤ) * (18 : ℤ)^m

private theorem profiles_of_integer {lo hi : ℕ} {c : ℤ}
    (he : integralProfileChecks lo hi c) : profileChecks lo hi c := by
  intro A hA t hfit
  let D := ∏ p ∈ A, p
  let P := ∏ p ∈ A, (p-1)
  let m := t.val
  have hint := he A hA t hfit
  change (c - (refund hi A : ℤ) + (1 + (wholeError (A.card+m) : ℤ))) * (D : ℤ) * (19 : ℤ)^m <
    (lo : ℤ) * (P : ℤ) * (18 : ℤ)^m at hint
  have hrat : ((c : ℚ) - (refund hi A : ℚ) + (1 + (wholeError (A.card+m) : ℚ))) *
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
  change (c : ℚ) - (refund hi A : ℚ) + (1 + initialError (A.card+m)) <
    (lo : ℚ) * largeRho A * (18/19 : ℚ)^m
  apply (mul_lt_mul_iff_of_pos_right (mul_pos hD (by positivity : (0 : ℚ) < 19^m))).mp
  calc
    _ = ((c : ℚ) - (refund hi A : ℚ) + (1 + (wholeError (A.card+m) : ℚ))) *
        (D : ℚ) * (19 : ℚ)^m := by rw [initialError_asNat]; ring
    _ < _ := hrat
    _ = (lo : ℚ) * (largeRho A * (D : ℚ)) * ((18/19 : ℚ)^m * (19 : ℚ)^m) := by
      rw [hρ, hpower]
    _ = _ := by ring

private def verifiedRow (c : ℕ × ℕ × ℤ) : Prop :=
  300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧ integralProfileChecks c.1 c.2.1 c.2.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow300 : verifiedRow (300, 305, 225) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow306 : verifiedRow (306, 310, 229) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow311 : verifiedRow (311, 319, 234) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow320 : verifiedRow (320, 328, 241) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow329 : verifiedRow (329, 337, 246) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow338 : verifiedRow (338, 346, 254) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow347 : verifiedRow (347, 359, 261) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow360 : verifiedRow (360, 373, 272) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow374 : verifiedRow (374, 391, 283) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow392 : verifiedRow (392, 412, 296) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow413 : verifiedRow (413, 431, 313) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow432 : verifiedRow (432, 454, 327) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow455 : verifiedRow (455, 482, 345) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow483 : verifiedRow (483, 514, 368) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow515 : verifiedRow (515, 547, 393) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow548 : verifiedRow (548, 589, 419) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow590 : verifiedRow (590, 638, 451) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow639 : verifiedRow (639, 701, 491) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow702 : verifiedRow (702, 770, 539) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow771 : verifiedRow (771, 847, 593) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow848 : verifiedRow (848, 938, 654) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow939 : verifiedRow (939, 1052, 726) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1053 : verifiedRow (1053, 1187, 814) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1188 : verifiedRow (1188, 1352, 923) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1353 : verifiedRow (1353, 1558, 1053) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1559 : verifiedRow (1559, 1807, 1215) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1808 : verifiedRow (1808, 2114, 1413) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2115 : verifiedRow (2115, 2501, 1658) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2502 : verifiedRow (2502, 2808, 1851) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2809 : verifiedRow (2809, 3172, 2082) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow3173 : verifiedRow (3173, 3609, 2356) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow3610 : verifiedRow (3610, 4147, 2689) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow4148 : verifiedRow (4148, 4796, 3094) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow4797 : verifiedRow (4797, 5012, 3500) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5013 : verifiedRow (5013, 5242, 3659) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5243 : verifiedRow (5243, 5488, 3828) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5489 : verifiedRow (5489, 5747, 4008) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5748 : verifiedRow (5748, 6034, 4200) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6035 : verifiedRow (6035, 6335, 4409) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6336 : verifiedRow (6336, 6668, 4633) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6669 : verifiedRow (6669, 7018, 4878) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7019 : verifiedRow (7019, 7409, 5136) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7410 : verifiedRow (7410, 7827, 5424) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7828 : verifiedRow (7828, 8494, 5764) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow8495 : verifiedRow (8495, 9237, 6259) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow9238 : verifiedRow (9238, 9999, 6771) := by
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
private theorem moderateRow10354 : verifiedRow (10354, 10727, 7550) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow10728 : verifiedRow (10728, 11114, 7824) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow11115 : verifiedRow (11115, 11519, 8107) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow11520 : verifiedRow (11520, 11945, 8403) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow11946 : verifiedRow (11946, 12397, 8716) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow12398 : verifiedRow (12398, 12862, 9045) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow12863 : verifiedRow (12863, 13356, 9387) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow13357 : verifiedRow (13357, 13876, 9748) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow13877 : verifiedRow (13877, 14422, 10129) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow14423 : verifiedRow (14423, 15009, 10531) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow15010 : verifiedRow (15010, 15619, 10960) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow15620 : verifiedRow (15620, 16798, 11486) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow16799 : verifiedRow (16799, 18079, 12355) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow18080 : verifiedRow (18080, 19463, 13300) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow19464 : verifiedRow (19464, 20438, 14241) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow20439 : verifiedRow (20439, 21479, 14959) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow21480 : verifiedRow (21480, 22580, 15721) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow22581 : verifiedRow (22581, 23741, 16528) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow23742 : verifiedRow (23742, 24967, 17379) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow24968 : verifiedRow (24968, 26262, 18277) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow26263 : verifiedRow (26263, 27634, 19226) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow27635 : verifiedRow (27635, 29079, 20232) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow29080 : verifiedRow (29080, 30616, 21294) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow30617 : verifiedRow (30617, 32242, 22420) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow32243 : verifiedRow (32243, 35140, 23788) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow35141 : verifiedRow (35141, 38308, 25928) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow38309 : verifiedRow (38309, 41241, 28189) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow41242 : verifiedRow (41242, 42541, 29073) := by
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
private theorem moderateRow44834 : verifiedRow (44834, 46026, 31451) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow46027 : verifiedRow (46027, 47248, 32287) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow47249 : verifiedRow (47249, 48199, 32930) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow48200 : verifiedRow (48200, 49166, 33594) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow49167 : verifiedRow (49167, 50159, 34270) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow50160 : verifiedRow (50160, 51167, 34961) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow51168 : verifiedRow (51168, 52203, 35664) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow52204 : verifiedRow (52204, 53271, 36390) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow53272 : verifiedRow (53272, 54359, 37134) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow54360 : verifiedRow (54360, 55479, 37895) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow55480 : verifiedRow (55480, 56613, 38674) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow56614 : verifiedRow (56614, 57775, 39466) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow57776 : verifiedRow (57776, 58965, 40276) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow58966 : verifiedRow (58966, 60187, 41107) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow60188 : verifiedRow (60188, 61431, 41959) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow61432 : verifiedRow (61432, 62712, 42828) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow62713 : verifiedRow (62713, 64023, 43723) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow64024 : verifiedRow (64024, 67574, 44966) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow67575 : verifiedRow (67575, 71339, 47465) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow71340 : verifiedRow (71340, 75315, 50111) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow75316 : verifiedRow (75316, 79515, 52905) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow79516 : verifiedRow (79516, 83407, 55774) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow83408 : verifiedRow (83408, 87502, 58507) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow87503 : verifiedRow (87503, 91798, 61380) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow91799 : verifiedRow (91799, 96318, 64397) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow96319 : verifiedRow (96319, 101051, 67567) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow101052 : verifiedRow (101052, 106038, 70891) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow106039 : verifiedRow (106039, 111271, 74389) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow111272 : verifiedRow (111272, 116761, 78059) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow116762 : verifiedRow (116762, 122530, 81916) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow122531 : verifiedRow (122531, 128599, 85964) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow128600 : verifiedRow (128600, 139288, 90869) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow139289 : verifiedRow (139289, 150873, 98423) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow150874 : verifiedRow (150874, 162886, 106531) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow162887 : verifiedRow (162887, 175856, 115014) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow175857 : verifiedRow (175857, 189863, 124175) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow189864 : verifiedRow (189864, 204988, 134067) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow204989 : verifiedRow (204989, 221323, 144749) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow221324 : verifiedRow (221324, 238981, 156288) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow238982 : verifiedRow (238982, 265720, 169903) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow265721 : verifiedRow (265721, 295469, 188916) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow295470 : verifiedRow (295470, 327979, 209985) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow327980 : verifiedRow (327980, 364067, 233090) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow364068 : verifiedRow (364068, 404108, 258737) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow404109 : verifiedRow (404109, 448564, 287197) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow448565 : verifiedRow (448565, 497933, 318796) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow497934 : verifiedRow (497934, 567913, 356149) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow567914 : verifiedRow (567914, 647169, 406122) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow647170 : verifiedRow (647170, 737464, 462796) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow737465 : verifiedRow (737465, 808306, 507256) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow808307 : verifiedRow (808307, 879578, 551992) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow879579 : verifiedRow (879579, 949517, 595873) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow949518 : verifiedRow (949518, 1000000, 627559) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

private theorem checks : ∀ c ∈ rows, 300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧
    integralProfileChecks c.1 c.2.1 c.2.2 := by
  change ∀ c ∈ rows, verifiedRow c
  unfold rows
  refine List.forall_mem_cons.mpr ⟨moderateRow300, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow306, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow311, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow320, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow329, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow338, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow347, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow360, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow374, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow392, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow413, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow432, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow455, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow483, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow515, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow548, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow590, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow639, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow702, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow771, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow848, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow939, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1053, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1188, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1353, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1559, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow1808, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow2115, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow2502, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow2809, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow3173, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow3610, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow4148, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow4797, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5013, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5243, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5489, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow5748, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6035, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6336, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6669, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7019, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7410, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7828, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow8495, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow9238, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10000, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10354, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10728, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow11115, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow11520, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow11946, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow12398, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow12863, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow13357, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow13877, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow14423, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow15010, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow15620, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow16799, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow18080, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow19464, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow20439, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow21480, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow22581, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow23742, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow24968, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow26263, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow27635, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow29080, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow30617, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow32243, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow35141, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow38309, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow41242, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow42542, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow43672, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow44834, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow46027, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow47249, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow48200, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow49167, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow50160, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow51168, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow52204, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow53272, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow54360, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow55480, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow56614, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow57776, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow58966, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow60188, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow61432, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow62713, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow64024, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow67575, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow71340, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow75316, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow79516, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow83408, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow87503, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow91799, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow96319, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow101052, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow106039, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow111272, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow116762, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow122531, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow128600, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow139289, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow150874, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow162887, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow175857, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow189864, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow204989, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow221324, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow238982, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow265721, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow295470, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow327980, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow364068, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow404109, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow448565, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow497934, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow567914, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow647170, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow737465, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow808307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow879579, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow949518, ?_⟩
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
        (1 + (if S.card=0 then 0 else (2:ℚ)^(S.card-1))) < (J:ℚ)*largeRho S := by
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
  change _ + (1 + initialError S.card) < _
  rw [← card]
  exact (add_le_add hleft le_rfl).trans_lt (hcase.trans_le hright)

end A085267Moderate

theorem OMA.solution : OMA.R_oeis_a085267_R1_H2_R1_H1_R1.H1 := by
  intro J S hlo hhi hS hB
  obtain ⟨c, hc, profile⟩ := A085267Moderate.moderate_sieve_budget hlo hhi hS hB
  exact profile (A085267Moderate.allCosts c hc)

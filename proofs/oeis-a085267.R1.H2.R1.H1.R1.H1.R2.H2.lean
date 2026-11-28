import OMAReductions.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R2
import Mathlib

/-!
Interval coverage and exact profile inequalities for the finite A085267 sieve.
Each interval supplies its strict comparison assuming its own upper bound.
The integer inequalities retain an additional unit for the second representation.
Source: https://oeis.org/A085267
Credit: @dwilfand-sys
-/

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
  (4797, 5587, 3587),
  (5588, 6550, 4186),
  (6551, 7717, 4913),
  (7718, 9127, 5796),
  (9128, 10826, 6860),
  (10827, 12856, 8141),
  (12857, 15277, 9669),
  (15278, 18145, 11490),
  (18146, 21509, 13642),
  (21510, 25501, 16174),
  (25502, 30187, 19170),
  (30188, 35691, 22687),
  (35692, 42133, 26816),
  (42134, 47422, 30206),
  (47423, 52933, 33733),
  (52934, 59017, 37645),
  (59018, 65747, 41966),
  (65748, 73183, 46743),
  (73184, 81368, 52018),
  (81369, 90412, 57829),
  (90413, 100372, 64244),
  (100373, 111355, 71314),
  (111356, 123461, 79107),
  (123462, 136790, 87694),
  (136791, 151490, 97154),
  (151491, 167648, 107578),
  (167649, 185462, 119043),
  (185463, 205073, 131680),
  (205074, 226637, 145588),
  (226638, 250388, 160887),
  (250389, 276548, 177736),
  (276549, 305347, 196294),
  (305348, 337067, 216724),
  (337068, 372019, 239230),
  (372020, 410518, 264028),
  (410519, 452948, 291344),
  (452949, 499724, 321452),
  (499725, 551285, 354645),
  (551286, 608135, 391232),
  (608136, 670852, 431581),
  (670853, 740049, 476093),
  (740050, 808306, 519980),
  (808307, 851143, 547552),
  (851144, 896309, 576581),
  (896310, 936787, 602616),
  (936788, 979091, 629830),
  (979092, 1000000, 643264)]

end A085267Moderate

namespace A085267Moderate

open A085267Sieve

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
private theorem moderateRow4797 : verifiedRow (4797, 5587, 3587) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5588 : verifiedRow (5588, 6550, 4186) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6551 : verifiedRow (6551, 7717, 4913) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7718 : verifiedRow (7718, 9127, 5796) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow9128 : verifiedRow (9128, 10826, 6860) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow10827 : verifiedRow (10827, 12856, 8141) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow12857 : verifiedRow (12857, 15277, 9669) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow15278 : verifiedRow (15278, 18145, 11490) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow18146 : verifiedRow (18146, 21509, 13642) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow21510 : verifiedRow (21510, 25501, 16174) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow25502 : verifiedRow (25502, 30187, 19170) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow30188 : verifiedRow (30188, 35691, 22687) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow35692 : verifiedRow (35692, 42133, 26816) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow42134 : verifiedRow (42134, 47422, 30206) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow47423 : verifiedRow (47423, 52933, 33733) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow52934 : verifiedRow (52934, 59017, 37645) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow59018 : verifiedRow (59018, 65747, 41966) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow65748 : verifiedRow (65748, 73183, 46743) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow73184 : verifiedRow (73184, 81368, 52018) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow81369 : verifiedRow (81369, 90412, 57829) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow90413 : verifiedRow (90413, 100372, 64244) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow100373 : verifiedRow (100373, 111355, 71314) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow111356 : verifiedRow (111356, 123461, 79107) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow123462 : verifiedRow (123462, 136790, 87694) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow136791 : verifiedRow (136791, 151490, 97154) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow151491 : verifiedRow (151491, 167648, 107578) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow167649 : verifiedRow (167649, 185462, 119043) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow185463 : verifiedRow (185463, 205073, 131680) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow205074 : verifiedRow (205074, 226637, 145588) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow226638 : verifiedRow (226638, 250388, 160887) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow250389 : verifiedRow (250389, 276548, 177736) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow276549 : verifiedRow (276549, 305347, 196294) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow305348 : verifiedRow (305348, 337067, 216724) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow337068 : verifiedRow (337068, 372019, 239230) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow372020 : verifiedRow (372020, 410518, 264028) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow410519 : verifiedRow (410519, 452948, 291344) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow452949 : verifiedRow (452949, 499724, 321452) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow499725 : verifiedRow (499725, 551285, 354645) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow551286 : verifiedRow (551286, 608135, 391232) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow608136 : verifiedRow (608136, 670852, 431581) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow670853 : verifiedRow (670853, 740049, 476093) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow740050 : verifiedRow (740050, 808306, 519980) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow808307 : verifiedRow (808307, 851143, 547552) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow851144 : verifiedRow (851144, 896309, 576581) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow896310 : verifiedRow (896310, 936787, 602616) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow936788 : verifiedRow (936788, 979091, 629830) := by
  refine ⟨by decide, by decide, ?_⟩
  unfold integralProfileChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow979092 : verifiedRow (979092, 1000000, 643264) := by
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
  refine List.forall_mem_cons.mpr ⟨moderateRow5588, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6551, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7718, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow9128, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10827, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow12857, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow15278, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow18146, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow21510, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow25502, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow30188, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow35692, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow42134, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow47423, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow52934, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow59018, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow65748, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow73184, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow81369, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow90413, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow100373, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow111356, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow123462, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow136791, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow151491, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow167649, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow185463, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow205074, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow226638, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow250389, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow276549, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow305348, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow337068, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow372020, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow410519, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow452949, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow499725, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow551286, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow608136, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow670853, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow740050, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow808307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow851144, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow896310, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow936788, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow979092, ?_⟩
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

theorem OMA.solution : OMA.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R2.H2 := by
  intro J S hlo hhi hS hB
  exact A085267Moderate.moderate_sieve_budget hlo hhi hS hB

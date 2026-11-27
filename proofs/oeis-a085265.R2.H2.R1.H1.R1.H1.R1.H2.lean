import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R1
import Mathlib

/-!
Interval coverage and exact profile inequalities for the finite A085265 sieve.
Each interval supplies its strict comparison assuming its own upper bound.
Credit: @dwilfand-sys
-/

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

/- Insert within A085265Moderate after profileChecks and before the closed
   row certificates. This file is a Lean source fragment. -/

private def largestProfileRank (D cap : ℕ) : ℕ :=
  if D * 19^4 ≤ cap then 4 else
  if D * 19^3 ≤ cap then 3 else
  if D * 19^2 ≤ cap then 2 else
  if D * 19 ≤ cap then 1 else 0

private theorem admissible_le_largest {D cap t : ℕ} (ht : t < 5)
    (h : D * 19^t ≤ cap) : t ≤ largestProfileRank D cap := by
  interval_cases t <;> try simp only [pow_one] at h
  all_goals
    unfold largestProfileRank <;> split_ifs <;> omega

private def endpointProfileChecks (lo hi : ℕ) (c : ℤ) : Prop :=
  ∀ A ∈ smallPrimes.powerset, (∏ p ∈ A, p) ≤ 2*hi+2 →
    let m := largestProfileRank (∏ p ∈ A, p) (2*hi+2)
    (c : ℚ) - (refund hi A : ℚ) + initialError (A.card + m) <
      (lo : ℚ) * largeRho A * (18/19 : ℚ)^m

private theorem initialError_nondecreasing {i j : ℕ} (h : i ≤ j) :
    initialError i ≤ initialError j := by
  have step (u : ℕ) : initialError u ≤ initialError (u+1) := by
    cases u with
    | zero => norm_num [initialError]
    | succ u =>
      have hpow : 0 ≤ (2 : ℚ)^u := by positivity
      have hd : (2 : ℚ)^u ≤ 2^u * 2 := by linarith
      simpa [initialError, pow_succ] using hd
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih => exact ih.trans (step (i+d))

private theorem profile_decay {i j : ℕ} (h : i ≤ j) :
    (18/19 : ℚ)^j ≤ (18/19 : ℚ)^i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, pow_succ]
    calc
      _ ≤ (18/19 : ℚ)^(i+d) * 1 :=
        mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ ≤ (18/19 : ℚ)^i := by simpa using ih

private theorem profileChecks_of_endpoints {lo hi : ℕ} {c : ℤ}
    (he : endpointProfileChecks lo hi c) : profileChecks lo hi c := by
  intro A hA t hadm
  let D := ∏ p ∈ A, p
  let m := largestProfileRank D (2*hi+2)
  have hprod : D ≤ 2*hi+2 := by
    have hp : 1 ≤ (19 : ℕ)^t.val := by positivity
    have hmul := Nat.mul_le_mul_left D hp
    have hbase : D ≤ D * 19^t.val := by simpa only [Nat.mul_one] using hmul
    exact hbase.trans hadm
  have hle : t.val ≤ m := admissible_le_largest t.isLt hadm
  have hlast := he A hA hprod
  change (c : ℚ) - (refund hi A : ℚ) + initialError (A.card + m) <
    (lo : ℚ) * largeRho A * (18/19 : ℚ)^m at hlast
  have known : ∀ p ∈ smallPrimes, 2 < p := by decide
  have hrho : 0 ≤ largeRho A := by
    unfold largeRho
    apply Finset.prod_nonneg
    intro p hp
    have hbig := known p (Finset.mem_powerset.mp hA hp)
    have hone : (1 : ℚ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    exact sub_nonneg.mpr ((div_le_one (by linarith : (0 : ℚ) < p)).mpr hone)
  exact (add_le_add_left (initialError_nondecreasing (Nat.add_le_add_left hle A.card)) _).trans_lt
    (hlast.trans_le (mul_le_mul_of_nonneg_left (profile_decay hle)
      (mul_nonneg (by positivity) hrho)))

private def wholeError (r : ℕ) : ℕ := if r = 0 then 0 else 2^(r-1)

private lemma initialError_asNat (r : ℕ) :
    initialError r = (wholeError r : ℚ) := by
  by_cases h : r = 0 <;> simp [initialError, wholeError, h]

private def integralEndpointChecks (lo hi : ℕ) (c : ℤ) : Prop :=
  ∀ A ∈ smallPrimes.powerset, (∏ p ∈ A, p) ≤ 2*hi+2 →
    let D := ∏ p ∈ A, p
    let P := ∏ p ∈ A, (p-1)
    let m := largestProfileRank D (2*hi+2)
    (c - (refund hi A : ℤ) + (wholeError (A.card+m) : ℤ)) * (D : ℤ) * (19 : ℤ)^m <
      (lo : ℤ) * (P : ℤ) * (18 : ℤ)^m

private theorem endpoints_of_integer {lo hi : ℕ} {c : ℤ}
    (he : integralEndpointChecks lo hi c) : endpointProfileChecks lo hi c := by
  intro A hA hfit
  let D := ∏ p ∈ A, p
  let P := ∏ p ∈ A, (p-1)
  let m := largestProfileRank D (2*hi+2)
  have hint := he A hA hfit
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
  300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧ profileChecks c.1 c.2.1 c.2.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow300 : verifiedRow (300, 307, 227) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow308 : verifiedRow (308, 314, 231) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow315 : verifiedRow (315, 323, 238) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow324 : verifiedRow (324, 332, 244) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow333 : verifiedRow (333, 341, 251) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow342 : verifiedRow (342, 355, 259) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow356 : verifiedRow (356, 368, 269) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow369 : verifiedRow (369, 385, 280) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow386 : verifiedRow (386, 409, 293) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow410 : verifiedRow (410, 430, 312) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow431 : verifiedRow (431, 454, 327) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow455 : verifiedRow (455, 484, 347) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow485 : verifiedRow (485, 517, 371) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow518 : verifiedRow (518, 550, 396) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow551 : verifiedRow (551, 592, 422) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow593 : verifiedRow (593, 643, 454) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow644 : verifiedRow (644, 710, 494) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow711 : verifiedRow (711, 782, 546) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow783 : verifiedRow (783, 865, 605) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow866 : verifiedRow (866, 964, 669) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow965 : verifiedRow (965, 1082, 747) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1083 : verifiedRow (1083, 1228, 842) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1229 : verifiedRow (1229, 1400, 957) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1401 : verifiedRow (1401, 1624, 1093) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1625 : verifiedRow (1625, 1885, 1268) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow1886 : verifiedRow (1886, 2213, 1477) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2214 : verifiedRow (2214, 2501, 1658) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2502 : verifiedRow (2502, 2810, 1852) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow2811 : verifiedRow (2811, 3175, 2085) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow3176 : verifiedRow (3176, 3613, 2359) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow3614 : verifiedRow (3614, 4153, 2693) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow4154 : verifiedRow (4154, 4805, 3100) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow4806 : verifiedRow (4806, 5602, 3595) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow5603 : verifiedRow (5603, 6574, 4198) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow6575 : verifiedRow (6575, 7745, 4933) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow7746 : verifiedRow (7746, 9163, 5819) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow9164 : verifiedRow (9164, 10868, 6888) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow10869 : verifiedRow (10869, 12905, 8173) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow12906 : verifiedRow (12906, 15340, 9709) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow15341 : verifiedRow (15341, 18230, 11541) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow18231 : verifiedRow (18231, 21628, 13710) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow21629 : verifiedRow (21629, 25645, 16264) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow25646 : verifiedRow (25646, 30356, 19280) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow30357 : verifiedRow (30357, 35902, 22818) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow35903 : verifiedRow (35903, 42385, 26976) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow42386 : verifiedRow (42386, 47546, 30284) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow47547 : verifiedRow (47547, 53065, 33821) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow53066 : verifiedRow (53066, 59170, 37742) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow59171 : verifiedRow (59171, 65906, 42074) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow65907 : verifiedRow (65907, 73363, 46859) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow73364 : verifiedRow (73364, 81562, 52146) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow81563 : verifiedRow (81563, 90625, 57967) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow90626 : verifiedRow (90626, 100606, 64397) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow100607 : verifiedRow (100607, 111608, 71479) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow111609 : verifiedRow (111609, 123731, 79287) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow123732 : verifiedRow (123732, 137092, 87888) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow137093 : verifiedRow (137093, 151816, 97368) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow151817 : verifiedRow (151817, 168016, 107812) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow168017 : verifiedRow (168017, 185867, 119305) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow185868 : verifiedRow (185868, 205514, 131967) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow205515 : verifiedRow (205515, 227137, 145904) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow227138 : verifiedRow (227138, 250933, 161241) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow250934 : verifiedRow (250934, 277159, 178125) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow277160 : verifiedRow (277160, 306017, 196728) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow306018 : verifiedRow (306018, 337817, 217203) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow337818 : verifiedRow (337818, 372854, 239765) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow372855 : verifiedRow (372855, 411418, 264618) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow411419 : verifiedRow (411419, 453940, 291986) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow453941 : verifiedRow (453941, 500809, 322156) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow500810 : verifiedRow (500810, 552482, 355415) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow552483 : verifiedRow (552483, 609460, 392084) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow609461 : verifiedRow (609461, 672335, 432525) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow672336 : verifiedRow (672336, 741674, 477145) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow741675 : verifiedRow (741675, 808306, 519980) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow808307 : verifiedRow (808307, 851143, 547552) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow851144 : verifiedRow (851144, 896314, 576584) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow896315 : verifiedRow (896315, 936791, 602620) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow936792 : verifiedRow (936792, 979100, 629835) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem moderateRow979101 : verifiedRow (979101, 1000000, 643264) := by
  refine ⟨by decide, by decide, profileChecks_of_endpoints (endpoints_of_integer ?_)⟩
  unfold integralEndpointChecks
  decide +kernel

private theorem checks : ∀ c ∈ rows, 300 ≤ c.1 ∧ c.2.1 ≤ 1000000 ∧
    profileChecks c.1 c.2.1 c.2.2 := by
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
  refine List.forall_mem_cons.mpr ⟨moderateRow5603, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow6575, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow7746, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow9164, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow10869, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow12906, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow15341, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow18231, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow21629, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow25646, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow30357, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow35903, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow42386, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow47547, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow53066, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow59171, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow65907, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow73364, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow81563, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow90626, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow100607, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow111609, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow123732, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow137093, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow151817, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow168017, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow185868, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow205515, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow227138, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow250934, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow277160, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow306018, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow337818, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow372855, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow411419, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow453941, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow500810, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow552483, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow609461, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow672336, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow741675, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow808307, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow851144, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow896315, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow936792, ?_⟩
  refine List.forall_mem_cons.mpr ⟨moderateRow979101, ?_⟩
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

set_option maxHeartbeats 2000000 in
theorem moderate_sieve_budget {J : ℕ} (hlo : 300 ≤ J) (hhi : J ≤ 1000000)
    {S : Finset ℕ} (hS : ∀ p ∈ S, 2 < p ∧ p.Prime) (hB : (∏ p ∈ S,p) ≤ 2*J+2) :
    ∃ c ∈ rows, (((∑ p ∈ largePrimeSet (2*c.2.1+1), (2*c.2.1/(p^2)+1)) : ℕ) : ℤ) ≤ c.2.2 →
    ((∑ p ∈ largePrimeSet (2*J+1) \ S, (2*J/(p^2)+1) : ℕ):ℚ) +
        (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) < (J:ℚ)*largeRho S := by
  obtain ⟨c,hc,hl,hu⟩ := covers_mem hlo hhi (show covers 300 rows by decide)
  refine ⟨c,hc,?_⟩
  intro htotal
  obtain ⟨hl₀,hu₀,hcases⟩ := checks c hc
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
    exact_mod_cast hsumZ
  change _ + initialError S.card < _
  rw [← card]
  exact (add_le_add hleft le_rfl).trans_lt (hcase.trans_le hright)

end A085265Moderate

theorem OMA.solution : OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R1.H2 := by
  intro J S hlo hhi hS hB
  exact A085265Moderate.moderate_sieve_budget hlo hhi hS hB

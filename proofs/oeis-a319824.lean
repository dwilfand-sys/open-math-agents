import OMAStatements.S_oeis_a319824
import Mathlib

/-!
# Subset sums of lucky-indexed lucky numbers

Source: https://oeis.org/A319824
Credit: @dwilfand-sys

Amiram Eldar posed the conjecture in 2018. Codex developed the sieve bound,
interval extension and finite certificate. Claude Code independently refereed
the mathematics and reproduced the numerical checks for David Wilfand.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace A319824Proof
open OMA.S_oeis_a319824

def total : ℕ → ℕ
  | 0 => 0
  | k + 1 => total k + u (k + 1)
end A319824Proof

namespace A319824Proof

open OMA.S_oeis_a319824

private lemma lift_mono (s : ℕ) : Monotone (liftRank s) := by
  intro x y h
  exact Nat.add_le_add h (Nat.div_le_div_right (Nat.sub_le_sub_right h 1))

private lemma rank_mono (ss : List ℕ) : Monotone (rankValue ss) := by
  induction ss with
  | nil => intro x y h; simp [rankValue]; omega
  | cons s ss ih =>
    intro x y h
    exact ih (lift_mono s h)

private lemma rank_add_step (ss : List ℕ) (s x : ℕ) :
    rankValue ss x ≤ rankValue (s :: ss) x := by
  apply rank_mono ss
  simp [liftRank]

private lemma rank_stage_grows (k x : ℕ) :
    rankValue (steps k) x ≤ rankValue (steps (k+1)) x :=
  rank_add_step _ _ _

private lemma rank_stage_mono (x : ℕ) : Monotone (fun k => rankValue (steps k) x) :=
  monotone_nat_of_le_succ (fun k => rank_stage_grows k x)

lemma lucky_mono : Monotone lucky := by
  intro a b h
  exact ((rank_mono (steps (a-2))) h).trans
    (rank_stage_mono b (Nat.sub_le_sub_right h 2))

lemma lucky_lower (n : ℕ) : 3*n ≤ lucky n + 3 := by
  by_cases hn : n < 3
  · interval_cases n <;> decide
  have h := rank_stage_mono n (show 1 ≤ n-2 by omega)
  change 2 * (n + (n - 1) / 2) - 1 ≤ lucky n at h
  omega

private def sieveWeight : List ℕ → ℚ
  | [] => 1
  | s :: ss => (1 + 1 / ((s-1 : ℕ) : ℚ)) * sieveWeight ss

private lemma weight_nonneg (ss : List ℕ) : 0 ≤ sieveWeight ss := by
  induction ss with
  | nil => norm_num [sieveWeight]
  | cons s ss ih =>
    change 0 ≤ (1 + 1 / ((s-1 : ℕ) : ℚ)) * sieveWeight ss
    positivity

private lemma cast_lift_le (s x : ℕ) :
    (liftRank s x : ℚ) ≤ (x : ℚ) * (1 + 1 / ((s-1 : ℕ) : ℚ)) := by
  by_cases hs : s - 1 = 0
  · simp [liftRank, hs]
  have hden : (0 : ℚ) < ((s-1 : ℕ) : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hnat : ((x-1)/(s-1))*(s-1) ≤ x :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have hcast : (((x-1)/(s-1) : ℕ) : ℚ) * ((s-1 : ℕ) : ℚ) ≤ (x : ℚ) := by
    exact_mod_cast hnat
  have hq := (le_div_iff₀ hden).2 hcast
  simp only [liftRank, Nat.cast_add]
  linarith [show (x : ℚ) * (1 + 1 / ((s-1 : ℕ) : ℚ)) = x + x / ((s-1 : ℕ) : ℚ) by ring]

private lemma folded_le (ss : List ℕ) (x : ℕ) :
    ((ss.foldl (fun y s => liftRank s y) x : ℕ) : ℚ) ≤ x * sieveWeight ss := by
  induction ss generalizing x with
  | nil => simp [sieveWeight]
  | cons s ss ih =>
    calc
      _ ≤ (liftRank s x : ℚ) * sieveWeight ss := ih _
      _ ≤ (x * (1 + 1 / ((s-1 : ℕ) : ℚ))) * sieveWeight ss :=
        mul_le_mul_of_nonneg_right (cast_lift_le s x) (weight_nonneg ss)
      _ = _ := by simp [sieveWeight, mul_assoc]

private lemma rv_le (ss : List ℕ) (x : ℕ) :
    (rankValue ss x : ℚ) ≤ x * (2 * sieveWeight ss) := by
  have hraw : rankValue ss x ≤ 2 * (ss.foldl (fun y s => liftRank s y) x) := Nat.sub_le _ _
  have hcast : (rankValue ss x : ℚ) ≤ 2 * ((ss.foldl (fun y s => liftRank s y) x : ℕ) : ℚ) := by
    exact_mod_cast hraw
  linarith [folded_le ss x]

private lemma weight_stage_step (k : ℕ) :
    (k : ℚ) * (1 + 1 / ((rankValue (steps k) (k+2) - 1 : ℕ) : ℚ))^3 ≤ (k:ℚ)+1 := by
  let s := rankValue (steps k) (k+2)
  have hs : 3*(k+2) ≤ s+3 := by
    simpa [s, lucky] using lucky_lower (k+2)
  have hnat : 3*k+2 ≤ s-1 := by omega
  have hden : (3:ℚ)*k+2 ≤ ((s-1 : ℕ) : ℚ) := by exact_mod_cast hnat
  have hpos : 0 < (3:ℚ)*k+2 := by positivity
  have hinv : (1:ℚ)/((s-1 : ℕ):ℚ) ≤ 1/(3*(k:ℚ)+2) :=
    div_le_div_of_nonneg_left (by norm_num) hpos hden
  change (k:ℚ) * (1 + 1 / ((s-1 : ℕ) : ℚ))^3 ≤ (k:ℚ)+1
  calc
    _ ≤ (k:ℚ) * (1 + 1 / (3*(k:ℚ)+2))^3 := by gcongr
    _ ≤ _ := by
      field_simp
      nlinarith [sq_nonneg (k:ℚ), Nat.cast_nonneg (α := ℚ) k]

private lemma weight_stage_bound (k : ℕ) (hk : 12 ≤ k) :
    8 * (2 * sieveWeight (steps k))^3 ≤ 125 * (k:ℚ) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    let t : ℚ := 1 + 1 / ((rankValue (steps k) (k+2) - 1 : ℕ) : ℚ)
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hmul := mul_le_mul_of_nonneg_right ih (pow_nonneg ht 3)
    have hstep : (k:ℚ)*t^3 ≤ (k:ℚ)+1 := weight_stage_step k
    change 8 * (2 * (t * sieveWeight (steps k)))^3 ≤ 125 * ((k+1:ℕ):ℚ)
    push_cast
    nlinarith only [hmul, hstep]

lemma lucky_upper (n : ℕ) (hn : 13 ≤ n) : 8*(lucky n)^3 ≤ 125*n^4 := by
  by_cases hsmall : n < 14
  · have h : n=13 := by omega
    subst n
    decide
  have hk : 12 ≤ n-2 := by omega
  let w := 2 * sieveWeight (steps (n-2))
  have hL : (lucky n : ℚ) ≤ (n:ℚ)*w := rv_le _ _
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℚ) (lucky n)) hL 3
  have hw : 8*w^3 ≤ 125*((n-2:ℕ):ℚ) := weight_stage_bound _ hk
  have hsub : ((n-2:ℕ):ℚ) ≤ (n:ℚ) := by exact_mod_cast Nat.sub_le n 2
  have hm := mul_le_mul_of_nonneg_left (hw.trans (mul_le_mul_of_nonneg_left hsub (by norm_num)))
    (show (0:ℚ) ≤ (n:ℚ)^3 by positivity)
  have hfinal : (8:ℚ)*(lucky n:ℚ)^3 ≤ 125*(n:ℚ)^4 := by nlinarith only [hpow, hm]
  exact_mod_cast hfinal

end A319824Proof

/- Finite certificate for Eldar's A319824, using only executable natural arithmetic.
   Include this section after the definition of A319824Proof.total. -/
namespace A319824Proof
open OMA.S_oeis_a319824

set_option maxRecDepth 10000 in
private def luckyDigits : List ℕ := [
  0, 1, 3, 7, 9, 13, 15, 21, 25, 31, 33, 37, 43, 49, 51, 63, 67, 69, 73, 75, 79, 87, 93, 99, 105, 111, 115, 127, 129, 133, 135, 141, 151, 159, 163, 169, 171, 189, 193, 195, 201, 205, 211, 219, 223, 231, 235, 237, 241, 259, 261, 267, 273, 283, 285, 289, 297, 303, 307, 319, 321, 327, 331, 339, 349, 357, 361, 367, 385, 391, 393, 399, 409, 415, 421, 427, 429, 433, 451, 463]

private def lookupLucky (i : ℕ) : ℕ := luckyDigits[i]?.getD 0

-- The latest deletion step is stored at the front, as in the sieve definition.
private def cachedSteps (k : ℕ) : List ℕ := ((luckyDigits.drop 2).take k).reverse

private theorem cached_step_rule : ∀ i : Fin 77,
    cachedSteps (i.val + 1) =
      rankValue (cachedSteps i.val) (i.val + 2) :: cachedSteps i.val := by
  decide +kernel

private theorem checked_steps (k : ℕ) (hk : k ≤ 77) : steps k = cachedSteps k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [steps, ih (by omega)]
    exact (cached_step_rule ⟨k, by omega⟩).symm

private theorem cached_value_rule : ∀ i : Fin 80,
    rankValue (cachedSteps (i.val - 2)) i.val = lookupLucky i.val := by
  decide +kernel

private theorem lucky_small (i : ℕ) (hi : i ≤ 79) : lucky i = lookupLucky i := by
  unfold lucky
  rw [checked_steps (i - 2) (by omega)]
  exact cached_value_rule ⟨i, by omega⟩

private def termAt (i : ℕ) : ℕ := lookupLucky (lookupLucky i)

private theorem seed_index_bound : ∀ i : Fin 21, lookupLucky i.val ≤ 79 := by
  decide +kernel

private theorem u_small (i : ℕ) (hi : i ≤ 20) : u i = termAt i := by
  unfold u termAt
  rw [lucky_small i (by omega), lucky_small _ (seed_index_bound ⟨i, by omega⟩)]

private def checkedTotal : ℕ → ℕ
  | 0 => 0
  | i + 1 => checkedTotal i + termAt (i + 1)

private theorem total_checked (i : ℕ) (hi : i ≤ 20) : total i = checkedTotal i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [total, checkedTotal, ih (by omega), u_small _ hi]

theorem seed_total : total 20 = 4006 := by
  rw [total_checked 20 (by decide)]
  decide +kernel

theorem seed_large : 373 < u 20 := by
  rw [u_small 20 (by decide)]
  decide +kernel

-- Bit i of row k encodes the presence of sum i in the first k terms.
-- Each hexadecimal numeral is recomputed from the preceding row in mask_rule.
private def maskDigits : Array ℕ := #[
  0x1,
  0x3,
  0x183,
  0x30600183,
  0x183000c1b0600183,
  0x3060018360c01b3600c1b0600183,
  0x183000c1b0600d9b3060d9b360c19b3600c1b0600183,
  0xc180060d83006cd98306cd9b060cdbb606ddb3060d9b360c19b3600c1b0600183,
  0x60c00306c180366cc18366cd8306eddb076fdb836edd9b06cddbb60edfb706ddbb060d9b360c19b3600c1b0600183,
  0xc180060d83006cd98306cd9b060ddbb60edfbf06fdff3e0fffff7c3ffffe3dffffbc7ffffc3efffff07cffbf60fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x60c00306c180366cc18366cd8306eddb076fdf83ffff9f0ffffffedfffffdfffffdffffffedffffffdff7fdffffffdbffffffdfffffdfffffdbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0xc180060d83006cd98306cd9b060ddbb60edfbf07ffff3e1ffffffdffffffffffffbffffffdffffffffffffbffffffbfffffffffffffffffffffffffffdffffffdffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x60c00306c180366cc18366cd8306eddb076fdf83ffff9f0ffffffeffffffffffffdffffffefffffffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x3060018360c01b3660c1b366c18376ed83b7efc1ffffcf87ffffff7fffffffffffefffffff7ffffffffffffffffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x183000c1b0600d9b3060d9b360c1bb76c1dbf7e0ffffe7c3ffffffbffffffffffff7ffffffbfffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0xc180060d83006cd98306cd9b060ddbb60edfbf07ffff3e1ffffffdffffffffffffbffffffdfffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x60c00306c180366cc18366cd8306eddb076fdf83ffff9f0ffffffeffffffffffffdffffffefffffffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x3060018360c01b3660c1b366c18376ed83b7efc1ffffcf87ffffff7fffffffffffefffffff7ffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x183000c1b0600d9b3060d9b360c1bb76c1dbf7e0ffffe7c3ffffffbffffffffffff7ffffffbfffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0xc180060d83006cd98306cd9b060ddbb60edfbf07ffff3e1ffffffdffffffffffffbffffffdfffffffffffffffffffbffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183,
  0x60c00306c180366cc18366cd8306eddb076fdf83ffff9f0ffffffeffffffffffffdffffffefffffffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffbffffffdffffffffffffbffffff87cffffe0fdfb706ddbb060d9b360c19b3600c1b0600183]

private def maskAt (k : ℕ) : ℕ := maskDigits[k]?.getD 0

private theorem mask_rule : ∀ i : Fin 20, maskAt (i.val + 1) =
    maskAt i.val ||| (maskAt i.val <<< termAt (i.val + 1)) := by
  decide +kernel

private theorem mask_spec (k : ℕ) (hk : k ≤ 20) (x : ℕ) :
    (maskAt k).testBit x = true ↔ attainable k x := by
  induction k generalizing x with
  | zero =>
    change Nat.testBit 1 x = true ↔ x = 0
    exact Nat.testBit_one_eq_true_iff_self_eq_zero
  | succ k ih =>
    have hstep : maskAt (k+1) = maskAt k ||| (maskAt k <<< u (k+1)) := by
      rw [u_small _ hk]
      exact mask_rule ⟨k, by omega⟩
    rw [hstep, Nat.testBit_or, Nat.testBit_shiftLeft]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      ih (by omega : k ≤ 20), attainable]
    constructor
    · rintro (h | ⟨hx, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x - u (k + 1), h, by omega⟩
    · rintro (h | ⟨y, h, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by simpa using h⟩

private theorem middle_ones :
    ((maskAt 20 >>> 374) &&& (2 ^ 3259 - 1)) = 2 ^ 3259 - 1 := by
  decide +kernel

theorem seed_interval : ∀ x, 374 ≤ x → x ≤ 3632 → attainable 20 x := by
  intro x hlow hhigh
  apply (mask_spec 20 (by decide) x).mp
  have h := congrArg (fun n : ℕ => n.testBit (x - 374)) middle_ones
  change (((maskAt 20 >>> 374) &&& (2 ^ 3259 - 1)).testBit (x - 374)) =
    (2 ^ 3259 - 1 : ℕ).testBit (x - 374) at h
  have hpos : x - 374 < 3259 := by omega
  simpa only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    show 374 + (x - 374) = x by omega, decide_eq_true hpos, Bool.and_true] using h

private def smallMissing : Finset ℕ :=
  (Finset.range 374).filter (fun x => 0 < x ∧ (maskAt 20).testBit x = false)

theorem seed_exceptions : ∃ e : Finset ℕ, e.card = 98 ∧ IsGreatest (e : Set ℕ) 373 ∧
    ∀ x ≤ 373, x ∈ e ↔ 0 < x ∧ ¬attainable 20 x := by
  refine ⟨smallMissing, ?_, ⟨?_, ?_⟩, ?_⟩
  · decide +kernel
  · change 373 ∈ smallMissing
    decide +kernel
  · intro x hx
    have hx' := (Finset.mem_filter.mp (show x ∈ smallMissing from hx)).1
    have := Finset.mem_range.mp hx'
    omega
  · intro x hx
    have h := mask_spec 20 (by decide) x
    have hlt : x < 374 := by omega
    simp only [smallMissing, Finset.mem_filter, Finset.mem_range, hlt, true_and]
    cases hbit : (maskAt 20).testBit x <;> simp_all

end A319824Proof

namespace A319824Proof

open OMA.S_oeis_a319824

private theorem indexed_mono : Monotone u := by
  intro i j h
  exact lucky_mono (lucky_mono h)

private theorem indexed_lower (n : ℕ) : 9 * n ≤ u n + 12 := by
  have h := lucky_lower n
  have h' := lucky_lower (lucky n)
  change 9 * n ≤ lucky (lucky n) + 12
  omega

private theorem indexed_upper (n : ℕ) (h : 21 ≤ n) :
    5 * u n ≤ 22 * n ^ 2 := by
  have hl := lucky_lower n
  have h1 := lucky_upper n (by omega)
  have h2 := lucky_upper (lucky n) (by omega)
  change 8 * (u n) ^ 3 ≤ 125 * (lucky n) ^ 4 at h2
  have h3 : 2 ^ 21 * (u n) ^ 9 ≤ 5 ^ 21 * n ^ 16 := by
    calc
      2 ^ 21 * (u n) ^ 9 = (8 * (u n) ^ 3) ^ 3 * 8 ^ 4 := by ring
      _ ≤ (125 * (lucky n) ^ 4) ^ 3 * 8 ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2 3)
      _ = 125 ^ 3 * (8 * (lucky n) ^ 3) ^ 4 := by ring
      _ ≤ 125 ^ 3 * (125 * n ^ 4) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 4)
      _ = 5 ^ 21 * n ^ 16 := by ring
  have h4 : 5 ^ 30 ≤ 2 ^ 21 * 22 ^ 9 * n ^ 2 := by
    calc
      5 ^ 30 ≤ 2 ^ 21 * 22 ^ 9 * 21 ^ 2 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
  have h5 : 2 ^ 21 * (5 * u n) ^ 9 ≤ 2 ^ 21 * (22 * n ^ 2) ^ 9 := by
    calc
      2 ^ 21 * (5 * u n) ^ 9 = 5 ^ 9 * (2 ^ 21 * (u n) ^ 9) := by ring
      _ ≤ 5 ^ 9 * (5 ^ 21 * n ^ 16) := Nat.mul_le_mul_left _ h3
      _ = 5 ^ 30 * n ^ 16 := by ring
      _ ≤ (2 ^ 21 * 22 ^ 9 * n ^ 2) * n ^ 16 := Nat.mul_le_mul_right _ h4
      _ = 2 ^ 21 * (22 * n ^ 2) ^ 9 := by ring
  have hp := Nat.le_of_mul_le_mul_left h5 (by decide : 0 < (2 : ℕ) ^ 21)
  by_contra! hh
  exact (not_lt_of_ge hp) (Nat.pow_lt_pow_left hh (by decide : 9 ≠ 0))

private theorem total_lower {k : ℕ} (hk : 20 ≤ k) :
    9 * k ^ 2 + 4712 ≤ 2 * total k + 15 * k := by
  induction k, hk using Nat.le_induction with
  | base => rw [seed_total]; decide
  | succ k hk ih =>
    have hu := indexed_lower (k + 1)
    rw [show total (k + 1) = total k + u (k + 1) from rfl]
    nlinarith only [hu, ih]

private theorem tail_overlaps {k : ℕ} (hk : 20 ≤ k) :
    u (k + 1) + 747 ≤ total k := by
  have hL := total_lower hk
  have hU := indexed_upper (k + 1) (by omega)
  have hs : 44 * (k + 1) ^ 2 + 7470 + 75 * k ≤ 45 * k ^ 2 + 23560 := by
    zify
    nlinarith only [sq_nonneg (2 * (k : ℤ) - 163)]
  nlinarith only [hL, hU, hs]

private theorem covers_interval {k : ℕ} (hk : 20 ≤ k) :
    ∀ x, 374 ≤ x → x + 374 ≤ total k → attainable k x := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro x hlo hhi
    rw [seed_total] at hhi
    exact seed_interval x hlo (by omega)
  | succ k hk ih =>
    intro x hlo hhi
    change x + 374 ≤ total k + u (k + 1) at hhi
    change attainable k x ∨ ∃ y, attainable k y ∧ x = y + u (k + 1)
    by_cases hold : x + 374 ≤ total k
    · exact Or.inl (ih x hlo hold)
    · have hb := tail_overlaps hk
      exact Or.inr ⟨x - u (k + 1), ih _ (by omega) (by omega), by omega⟩

private theorem total_grows {k : ℕ} (hk : 20 ≤ k) : k + 374 ≤ total k := by
  induction k, hk using Nat.le_induction with
  | base => rw [seed_total]; decide
  | succ k hk ih =>
    have hpos := indexed_lower (k + 1)
    change k + 1 + 374 ≤ total k + u (k + 1)
    omega

private theorem attainable_large (x : ℕ) (hx : 374 ≤ x) : ∃ k, attainable k x := by
  have h20 : 20 ≤ x := by omega
  exact ⟨x, covers_interval h20 x hx (total_grows h20)⟩

private theorem to_later_prefix {j k x : ℕ} (hjk : j ≤ k)
    (hx : attainable j x) : attainable k x := by
  induction k, hjk using Nat.le_induction with
  | base => exact hx
  | succ k hk ih => exact Or.inl ih

private theorem small_in_seed (x k : ℕ) (hx : x ≤ 373) (ha : attainable k x) :
    attainable 20 x := by
  by_cases hk : k ≤ 20
  · exact to_later_prefix hk ha
  · have h20 : 20 ≤ k := by omega
    clear hk
    revert ha
    induction k, h20 using Nat.le_induction with
    | base => exact id
    | succ k hk ih =>
      intro hc
      change attainable k x ∨ ∃ y, attainable k y ∧ x = y + u (k + 1) at hc
      rcases hc with hc | ⟨y, _, hy⟩
      · exact ih hc
      · have hlarge := seed_large
        have hnext := indexed_mono (show 20 ≤ k + 1 by omega)
        omega

theorem proof_main : exceptions.Finite ∧ exceptions.ncard = 98 ∧
    IsGreatest exceptions 373 := by
  obtain ⟨e, hcard, hmax, he⟩ := seed_exceptions
  have hset : exceptions = (e : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      have hs : x ≤ 373 := by
        by_contra! hl
        exact hn (attainable_large x (by omega))
      exact (he x hs).2 ⟨hx, fun ha => hn ⟨20, ha⟩⟩
    · intro hx
      have hs : x ≤ 373 := hmax.2 hx
      obtain ⟨hp, ha⟩ := (he x hs).1 hx
      refine ⟨hp, ?_⟩
      rintro ⟨k, hk⟩
      exact ha (small_in_seed x k hs hk)
  rw [hset, Set.ncard_coe_finset]
  exact ⟨e.finite_toSet, hcard, hmax⟩

end A319824Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a319824.main := by
  exact A319824Proof.proof_main

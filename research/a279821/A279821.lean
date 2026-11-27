import Mathlib

/-!
# Two central trinomial coefficient conjectures in OEIS A279821

Zhi-Wei Sun, OEIS A279821, comments dated December 19, 2016.
https://oeis.org/A279821

The central trinomial coefficient is the coefficient of X^n in
(1 + X + X^2)^n. In the first conjecture the exclusion on the square
root means that m is not the square of a prime. The second conjecture
uses modulus n^2 for every composite n.
-/

namespace A279821

noncomputable def centralTrinomial (n : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ n).coeff n

def listed : Finset ℕ :=
  {12, 30, 902, 1360, 2450, 3730, 21475, 74945, 82208, 88282, 254677}

def exhaustive : Prop :=
  ∀ m : ℕ,
    (1 < m ∧ ¬ m.Prime ∧ (∀ q : ℕ, q.Prime → q ^ 2 ≠ m) ∧
      Nat.ModEq m (centralTrinomial m) 1) ↔ m ∈ listed

def compositeSquareModulus : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime → ¬ Nat.ModEq (n ^ 2) (centralTrinomial n) 1

end A279821

/-!
The digit rule for the ordinary central trinomial coefficients is Theorem 4.7
of E. Deutsch and B. E. Sagan, “Congruences for Catalan and Motzkin numbers
and related sequences”, Journal of Number Theory 117 (2006), 191–215.
https://doi.org/10.1016/j.jnt.2005.06.005
-/

namespace A279821

open Polynomial
open scoped BigOperators

theorem lucas_step (p k d : ℕ) (hp : p.Prime) (hd : d < p) :
    (centralTrinomial (p * k + d) : ZMod p) =
      (centralTrinomial k : ZMod p) * (centralTrinomial d : ZMod p) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : Polynomial (ZMod p) := 1 + X + X ^ 2
  have hcast (n : ℕ) : (centralTrinomial n : ZMod p) = (f ^ n).coeff n := by
    change (Nat.castRingHom (ZMod p)) (((1 + X + X ^ 2 : Polynomial ℕ) ^ n).coeff n) = _
    rw [← Polynomial.coeff_map]
    simp [f]
  have hFrob : frobenius (ZMod p) p = RingHom.id (ZMod p) := by
    apply RingHom.ext
    intro x
    change x ^ p = x
    apply ZMod.pow_card
  have hpow : f ^ (p * k + d) = expand (ZMod p) p (f ^ k) * f ^ d := by
    rw [pow_add, Nat.mul_comm p k, pow_mul, ← Polynomial.map_frobenius_expand p,
      hFrob, Polynomial.map_id]
  have hdeg : f.natDegree ≤ 2 := by
    change (1 + X + X ^ 2 : Polynomial (ZMod p)).natDegree ≤ 2
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le <;> norm_num
    · norm_num
  have hdegd : (f ^ d).natDegree ≤ d * 2 := Polynomial.natDegree_pow_le_of_le d hdeg
  rw [hcast, hcast, hcast, hpow, Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (p * k, d)]
  · exact congrArg (fun c => c * (f ^ d).coeff d)
      (Polynomial.coeff_expand_mul' hp.pos (f ^ k) k)
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = p * k + d := Finset.mem_antidiagonal.mp hab
    change (expand (ZMod p) p (f ^ k)).coeff a * (f ^ d).coeff b = 0
    by_cases hpa : p ∣ a
    · obtain ⟨t, rfl⟩ := hpa
      by_cases hbd : b ≤ d * 2
      · have ht : t = k := by
          by_contra htk
          rcases lt_or_gt_of_ne htk with hlt | hgt
          · have hh := Nat.mul_le_mul_left p (show t + 1 ≤ k by omega)
            rw [Nat.mul_succ] at hh
            omega
          · have hh := Nat.mul_le_mul_left p (show k + 1 ≤ t by omega)
            rw [Nat.mul_succ] at hh
            omega
        subst t
        have hb : b = d := by omega
        exact (hne (by simp [hb])).elim
      · have hz : (f ^ d).coeff b = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegd (by omega))
        rw [hz, mul_zero]
    · rw [Polynomial.coeff_expand hp.pos, if_neg hpa, zero_mul]
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr rfl)).elim

end A279821

namespace A279821

open Finset Polynomial
open scoped BigOperators

-- This component follows the shared definition
--   centralTrinomial n = ((1 + X + X^2 : Polynomial ℕ)^n).coeff n.

/-- A closed natural-number expression with one factor per index. -/
private def fallingChoose (n k : ℕ) : ℕ :=
  n.descFactorial k / k.factorial

private def centralPartial (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    centralPartial n k + fallingChoose k (n-k) * fallingChoose n k

private theorem centralPartial_eq (n k : ℕ) :
    centralPartial n k = ∑ i ∈ range k, i.choose (n-i) * n.choose i := by
  induction k with
  | zero => simp [centralPartial]
  | succ k ih =>
    rw [centralPartial, sum_range_succ, ih]
    simp only [fallingChoose, Nat.choose_eq_descFactorial_div_factorial]

/-- Expand first in powers of (X+1)X, then read the coefficient of X^(n-i). -/
private theorem central_eval (n : ℕ) : centralTrinomial n = centralPartial n (n+1) := by
  rw [centralPartial_eq]
  change ((1 + X + X^2 : Polynomial ℕ)^n).coeff n = _
  have hp : (1 + X + X^2 : Polynomial ℕ) = (X+1)*X+1 := by ring
  rw [hp, add_pow, finsetSum_coeff]
  apply sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  simp [mul_pow, coeff_mul_X_pow', coeff_X_add_one_pow, hin]

set_option maxRecDepth 10000 in
theorem central_0 : centralTrinomial 0 = 1 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_1 : centralTrinomial 1 = 1 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_14 : centralTrinomial 14 = 616227 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_19 : centralTrinomial 19 = 128996853 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_20 : centralTrinomial 20 = 377379369 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_25 : centralTrinomial 25 = 82176836301 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_30 : centralTrinomial 30 = 18252025766941 := by rw [central_eval] <;> rfl

set_option maxRecDepth 10000 in
theorem central_31 : centralTrinomial 31 = 53876592856681 := by rw [central_eval] <;> rfl

end A279821

/-! Append after the central trinomial digit lemma and the eight small coefficients.
Zhi-Wei Sun's eleven-term exhaustion conjecture in A279821 fails at a product
of two distinct primes. This witness concerns congruence modulo the integer.
-/

namespace A279821

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem witness_1316632279 : Nat.ModEq 1316632279 (centralTrinomial 1316632279) 1 := by
  have hp : Nat.Prime 31 := by norm_num
  have hq : Nat.Prime 42472009 := by norm_num
  have h31 : (centralTrinomial 1316632279 : ZMod 31) = 1 := by
    rw [show 1316632279 = 31*42472009+0 by decide, lucas_step 31 42472009 0 hp (by decide),
      show 42472009 = 31*1370064+25 by decide, lucas_step 31 1370064 25 hp (by decide),
      show 1370064 = 31*44195+19 by decide, lucas_step 31 44195 19 hp (by decide),
      show 44195 = 31*1425+20 by decide, lucas_step 31 1425 20 hp (by decide),
      show 1425 = 31*45+30 by decide, lucas_step 31 45 30 hp (by decide),
      show 45 = 31*1+14 by decide, lucas_step 31 1 14 hp (by decide),
      central_0, central_1, central_14, central_19, central_20, central_25, central_30]
    decide
  have hbig : (centralTrinomial 1316632279 : ZMod 42472009) = 1 := by
    rw [show 1316632279 = 42472009*31+0 by decide,
      lucas_step 42472009 31 0 hq (by decide), central_0, central_31]
    decide
  have hcop : Nat.Coprime 31 42472009 := by decide
  change Nat.ModEq (31*42472009) (centralTrinomial 1316632279) 1
  apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
  constructor
  · apply (ZMod.natCast_eq_natCast_iff _ _ 31).mp
    simpa only [Nat.cast_one] using h31
  · apply (ZMod.natCast_eq_natCast_iff _ _ 42472009).mp
    simpa only [Nat.cast_one] using hbig

theorem refute_exhaustion : ¬exhaustive := by
  intro conjecture
  have hcomp : ¬ Nat.Prime 1316632279 := by
    intro hp
    have hfac : 31 ∣ 1316632279 := ⟨42472009, by decide⟩
    rcases (Nat.dvd_prime hp).mp hfac with he | he <;> omega
  have hsq (q : ℕ) : q^2 ≠ 1316632279 := by
    by_cases hq : q ≤ 36285
    · have h := Nat.mul_self_le_mul_self hq
      rw [sq]
      omega
    · have h := Nat.mul_self_le_mul_self (show 36286 ≤ q by omega)
      rw [sq]
      omega
  have hm := (conjecture 1316632279).mp
    ⟨by decide, hcomp, fun q _ => hsq q, witness_1316632279⟩
  have hn : 1316632279 ∉ listed := by decide
  exact hn hm

end A279821

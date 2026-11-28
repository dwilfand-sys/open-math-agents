import OMAStatements.S_oeis_a242076
import Mathlib

/-!
# The unique exponent with exactly one factor of two in A242076

Credit: @dwilfand-sys (formalization by Codex). J. Lowell posed the question.
The central algebraic identity is Sophie Germain's factorization. Related
earlier work includes Jack Brennen's 2017 argument recorded in OEIS A283657
and Lowell's observation on largest odd divisors in OEIS A242076.
Source: https://oeis.org/A242076
Related source: https://oeis.org/A283657
-/

namespace A242076Proof

private lemma large_factors {a b q : ℕ} (ha : 5 < a) (hb : 5 < b)
    (hq : q.Prime) (he : a * b = 5 * q) : False := by
  have exclude (u v : ℕ) (hu : 5 < u) (hv : 5 < v) (h : u * v = 5 * q)
      (hd : q ∣ u) : False := by
    obtain ⟨t, rfl⟩ := hd
    have ht : 1 ≤ t := by
      by_contra! hn
      have hz : t = 0 := by omega
      simp [hz] at hu
    have hc : t * v = 5 := by
      apply Nat.eq_of_mul_eq_mul_left hq.pos
      calc q * (t * v) = q * t * v := by ring
           _ = 5 * q := h
           _ = q * 5 := by ring
    have hl : v ≤ t * v := by
      simpa using Nat.mul_le_mul_right v ht
    omega
  have hd : q ∣ a * b := by rw [he]; exact dvd_mul_left _ _
  rcases hq.dvd_mul.mp hd with h | h
  · exact exclude a b ha hb he h
  · exact exclude b a hb ha (by simpa [Nat.mul_comm] using he) h

private lemma sophie {y q : ℕ} (hy : 3 ≤ y) (hq : q.Prime)
    (h : 4 * y ^ 4 + 1 = 5 * q) : False := by
  let u := y - 3
  have hu : y = u + 3 := by dsimp [u]; omega
  let a := 2 * u ^ 2 + 10 * u + 13
  let b := 2 * u ^ 2 + 14 * u + 25
  apply large_factors (a := a) (b := b) (q := q) (by dsimp [a]; omega)
    (by dsimp [b]; omega) hq
  calc a * b = 4 * (u + 3) ^ 4 + 1 := by dsimp [a, b]; ring
       _ = 5 * q := by rw [← hu]; exact h

private lemma mod_five (r : ℕ) : 16 ^ r % 5 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private lemma mod_three (r : ℕ) : 16 ^ r % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private lemma only_six {k : ℕ} (hk : OMA.S_oeis_a242076.isTerm k)
    (h2 : 2 ∣ k) (h4 : ¬ 4 ∣ k) : k = 6 := by
  obtain ⟨j, q, hq, hproduct⟩ := hk
  let r := k / 4
  have hk' : k = 4 * r + 2 := by dsimp [r]; omega
  have hleft : 2 ^ k + 1 = 4 * 16 ^ r + 1 := by
    conv_lhs => rw [hk', pow_add, pow_mul]
    norm_num
    <;> ring
  rw [hleft] at hproduct
  cases j with
  | zero =>
    have hmod := congrArg (fun z : ℕ => z % 3) hproduct
    change (4 * 16 ^ r + 1) % 3 = (3 * q) % 3 at hmod
    have hm := mod_three r
    omega
  | succ j =>
    cases j with
    | zero =>
      have he : 4 * 16 ^ r + 1 = 5 * q := by simpa using hproduct
      have hr0 : r ≠ 0 := by
        rintro hr
        rw [hr] at he
        norm_num at he
        have := hq.two_le
        omega
      by_cases hr : r = 1
      · omega
      exfalso
      have hr2 : 2 ≤ r := by omega
      have hy : 3 ≤ (2 : ℕ) ^ r := by
        calc 3 ≤ (2 : ℕ) ^ 2 := by decide
             _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr2
      apply sophie hy hq
      have hp : ((2 : ℕ) ^ r) ^ 4 = 16 ^ r := by
        rw [← pow_mul, Nat.mul_comm r 4, pow_mul]; norm_num
      rwa [hp]
    | succ j =>
      let e := 2 ^ j
      have hF : (2 : ℕ) ^ (2 ^ (j + 1 + 1)) = 16 ^ e := by
        have hexp : (2 : ℕ) ^ (j + 1 + 1) = 4 * e := by
          dsimp [e]; rw [pow_succ, pow_succ]; ring
        rw [hexp, pow_mul]; norm_num
      change 4 * 16 ^ r + 1 = (2 ^ (2 ^ (j + 1 + 1)) + 1) * q at hproduct
      rw [hF] at hproduct
      have hd : 5 ∣ (16 ^ e + 1) * q := by
        rw [← hproduct]
        have hm := mod_five r
        omega
      have hq5 : q = 5 := by
        rcases (show Nat.Prime 5 by decide).dvd_mul.mp hd with h | h
        · exfalso
          have hm := mod_five e
          omega
        · exact ((Nat.dvd_prime hq).mp h).resolve_left (by decide) |>.symm
      rw [hq5] at hproduct
      have hepos : 0 < e := by dsimp [e]; positivity
      have hep : 0 < (16 : ℕ) ^ e := by positivity
      cases hr : r with
      | zero => simp only [hr, pow_zero, mul_one] at hproduct; omega
      | succ t =>
        have he : e = (e - 1) + 1 := by omega
        rw [hr, pow_succ, he, pow_succ] at hproduct
        omega

end A242076Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a242076.main := by
  intro k
  constructor
  · rintro ⟨hk, h2, h4⟩
    exact A242076Proof.only_six hk h2 h4
  · rintro rfl
    exact ⟨⟨1, 13, by decide, by decide⟩, by decide, by decide⟩

import OMAReductions.R_oeis_a085265_R2
import Mathlib

/-!
Finite part of A085265, through 365000. The root statement was formalized by
@niclorusso. The mask and its proof come from the full proof prepared by Codex.
Credit: @dwilfand-sys
-/

namespace A085265Sieve

/-! A bit at index `n` records a possible failure. The sieve and the fourteen
translations are computations on natural-number literals in the Lean kernel. -/

private def lowBits (width : ℕ) : ℕ := ((1 : ℕ) <<< width) - 1

private theorem lowBits_at (width n : ℕ) :
    (lowBits width).testBit n = decide (n < width) := by
  simpa only [lowBits, Nat.shiftLeft_eq, one_mul] using
    Nat.testBit_two_pow_sub_one width n

/-- One periodic row. Doubling the stride separates the even and odd indices
of its multiples. Stop once the next stride would leave the interval. -/
private def multiplesRow : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, d =>
    if 365000 < d then 1 else
      let row := multiplesRow fuel (2*d)
      row ||| (row <<< d)

private theorem multiplesRow_marks (fuel d k : ℕ) (hd : 0 < d)
    (hk : k < 2^fuel) (hbound : d*k ≤ 365000) :
    (multiplesRow fuel d).testBit (d*k) = true := by
  induction fuel generalizing d k with
  | zero =>
    have hk0 : k = 0 := by
      rw [pow_zero] at hk
      omega
    simp [multiplesRow, hk0]
  | succ fuel ih =>
    by_cases hstop : 365000 < d
    · have hk0 : k = 0 := by
        by_contra hne
        have hle : d ≤ d*k := by
          simpa using Nat.mul_le_mul_left d (show 1 ≤ k by omega)
        omega
      simp [multiplesRow, hstop, hk0]
    · have hquot : k/2 < 2^fuel := by
        rw [pow_succ] at hk
        omega
      have hreorder : (2*d)*(k/2) = d*(2*(k/2)) := by ring
      have hle : (2*d)*(k/2) ≤ d*k := by
        rw [hreorder]
        exact Nat.mul_le_mul_left _ (by omega)
      have hrec := ih (2*d) (k/2) (by omega) hquot (hle.trans hbound)
      rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
      · have hki : 2*(k/2) = k := by omega
        have hindex : d*k = (2*d)*(k/2) := by rw [hreorder, hki]
        simp only [multiplesRow, if_neg hstop, Nat.testBit_or, hindex, hrec, Bool.true_or]
      · have hki : 2*(k/2)+1 = k := by omega
        have hindex : (2*d)*(k/2)+d = d*k := by
          calc
            _ = d*(2*(k/2)+1) := by ring
            _ = _ := by rw [hki]
        have hsub : d*k-d = (2*d)*(k/2) := by omega
        have hge : d ≤ d*k := by omega
        simp [multiplesRow, hstop, Nat.testBit_or, Nat.testBit_shiftLeft,
          hge, hsub, hrec]

/-- Rows for every possible square divisor `d²`, where `2 ≤ d ≤ count+1`. -/
private def squareDivisorMask : ℕ → ℕ
  | 0 => 1
  | count+1 => squareDivisorMask count ||| multiplesRow 19 ((count+2)^2)

private theorem squareDivisorMask_marks (count d k : ℕ)
    (hd : 2 ≤ d) (hcount : d ≤ count+1) (hbound : d^2*k ≤ 365000) :
    (squareDivisorMask count).testBit (d^2*k) = true := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [squareDivisorMask, Nat.testBit_or]
    by_cases h : d = count+2
    · subst d
      have hpos : 0 < (count+2)^2 := by positivity
      have hmult : k ≤ (count+2)^2*k := by
        simpa using Nat.mul_le_mul_right k (show 1 ≤ (count+2)^2 by omega)
      have hsize : k < 2^19 := by norm_num; omega
      rw [multiplesRow_marks 19 _ k hpos hsize hbound, Bool.or_true]
    · rw [ih (by omega), Bool.true_or]

private theorem nonsquarefree_marked {n : ℕ} (hn : 0 < n)
    (hmax : n ≤ 365000) (hbad : ¬ Squarefree n) :
    (squareDivisorMask 603).testBit n = true := by
  rw [Nat.squarefree_iff_prime_squarefree] at hbad
  push_neg at hbad
  obtain ⟨p, hp, hdiv⟩ := hbad
  have hd : p^2 ∣ n := by simpa only [pow_two] using hdiv
  have hsq := Nat.le_of_dvd hn hd
  have hmaxp : p ≤ 604 := by
    by_contra! h
    have h605 : 605^2 ≤ p^2 := Nat.pow_le_pow_left (by omega) 2
    norm_num at h605
    omega
  obtain ⟨k, rfl⟩ := hd
  exact squareDivisorMask_marks 603 p k hp.two_le hmaxp hmax

/-- Intersect the masks for the first `k` positive squares. The low bits in
each translation account for the requirement that the remainder be positive. -/
private def failureMask : ℕ → ℕ → ℕ
  | 0, _ => lowBits 365001
  | k+1, mask => failureMask k mask &&&
      ((mask <<< ((k+1)^2)) ||| lowBits ((k+1)^2+1))

private theorem failureMask_marks (k n : ℕ) (hmax : n ≤ 365000)
    (hfail : ∀ w : ℕ, 0 < w → w ≤ k → w^2 < n → ¬ Squarefree (n-w^2)) :
    (failureMask k (squareDivisorMask 603)).testBit n = true := by
  induction k with
  | zero =>
    rw [failureMask, lowBits_at, decide_eq_true_eq]
    omega
  | succ k ih =>
    have hold := ih (fun w hw hle hlt => hfail w hw (by omega) hlt)
    rw [failureMask, Nat.testBit_and, hold, Bool.true_and, Nat.testBit_or,
      Nat.testBit_shiftLeft, lowBits_at]
    by_cases hfit : (k+1)^2 < n
    · have hm := nonsquarefree_marked (n := n-(k+1)^2) (by omega)
          (by omega) (hfail (k+1) (by omega) le_rfl hfit)
      simp [hfit.le, hm]
    · have hlow : n < (k+1)^2+1 := by omega
      simp [hlow]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_mask_certificate : failureMask 14 (squareDivisorMask 603) = 8195 := by
  decide +kernel

private theorem finite_mask_exceptions (n : ℕ) (h : (8195 : ℕ).testBit n = true) :
    n = 0 ∨ n = 1 ∨ n = 13 := by
  have bits : (8195 : ℕ) = (2^0 ||| 2^1 ||| 2^13) := by decide
  rw [bits] at h
  simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at h
  omega

/-- Every positive input through 365000 other than 1 and 13 has a positive
squarefree remainder after subtracting a square with root at most 14. -/
theorem squarefree_finite {n : ℕ} (hn : 0 < n) (hN : n ≤ 365000)
    (h1 : n ≠ 1) (h13 : n ≠ 13) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 14 ∧ k^2 < n ∧ Squarefree (n-k^2) := by
  by_contra h
  have hmask := failureMask_marks 14 n hN (fun w hw hle hlt hs =>
    h ⟨w, hw, hle, hlt, hs⟩)
  rw [finite_mask_certificate] at hmask
  rcases finite_mask_exceptions n hmask with h0 | he1 | he13 <;> omega

end A085265Sieve

theorem OMA.solution : OMA.R_oeis_a085265_R2.H1 := by
  intro n hn hN h1 h13
  obtain ⟨k,hk,_,hlt,hs⟩ := A085265Sieve.squarefree_finite hn hN h1 h13
  exact ⟨k,hk,hlt,hs⟩

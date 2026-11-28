import OMAReductions.R_oeis_a085265_R2_H2_R1_H1_R1
import Mathlib

/-!
A dyadic certificate for the remaining A085265 intermediate-range sieve budget.
Separate the number of new odd primes from the exact floor and exceptional-prime
contributions. A small prime count seeds a finite chain of binomial bounds.
Proof development by Codex for @dwilfand-sys. Root statement by @niclorusso.
-/

open Finset
namespace OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R3

def H1 : Prop := ∀ m x e : ℕ, m ≤ x → x ≤ 2*m → 0 < e → 2^e ≤ m+1 →
    ((range (x+1)).filter (fun p : ℕ => 2 < p ∧ p.Prime)).card ≤
      ((range (m+1)).filter (fun p : ℕ => 2 < p ∧ p.Prime)).card + x/e

/-- It suffices to bound the score for any count controlled by small seeds and dyadic steps. -/
def H2 : Prop := ∀ C : ℕ → ℕ, Monotone C →
    (∀ x ≤ 10000, C x ≤ ((range (x+1)).filter (fun p : ℕ => 2 < p ∧ p.Prime)).card) →
    (∀ m x e : ℕ, m ≤ x → x ≤ 2*m → 0 < e → 2^e ≤ m+1 → C x ≤ C m + x/e) →
    ∀ (J : ℕ) (S : Finset ℕ), 300 ≤ J → J ≤ 1000000 →
      (∀ p ∈ S, 2 < p ∧ p.Prime) → (∏ p ∈ S, p) ≤ 2*J+2 →
      let A := (range (2*J+2)).filter (fun p : ℕ => 2 < p ∧ p.Prime)
      (((C (2*J+1) + ∑ p ∈ A, 2*J/(p^2)) -
        (∑ p ∈ A ∩ S, (2*J/(p^2)+1)) : ℕ) : ℚ) +
        (if S.card=0 then 0 else (2:ℚ)^(S.card-1)) < (J:ℚ) * ∏ p ∈ S, (1-1/(p:ℚ))

set_option maxHeartbeats 1500000 in
theorem main : H1 → H2 → OMA.R_oeis_a085265_R2_H2_R1_H1_R1.H1 := by
  intro dyad numerics J S hlo hhi hS hprod
  let ps := fun x : ℕ => (range (x+1)).filter (fun p : ℕ => 2 < p ∧ p.Prime)
  let A := ps (2*J+1)
  let w := fun p : ℕ => 2*J/(p^2)+1
  have mono : Monotone (fun x => (ps x).card) := by
    intro x y hxy
    apply card_le_card
    intro p hp
    obtain ⟨hr, ho⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hr).trans_le (Nat.succ_le_succ hxy)), ho⟩
  have hmargin := numerics (fun x => (ps x).card) mono (fun _ _ => le_rfl) dyad
    J S hlo hhi hS hprod
  have partition : (∑ p ∈ A \ S, w p) + (∑ p ∈ A ∩ S, w p) = ∑ p ∈ A, w p := by
    have disj : Disjoint (A \ S) (A ∩ S) :=
      Finset.disjoint_left.mpr fun _ hd hi => (mem_sdiff.mp hd).2 (mem_inter.mp hi).2
    have un : (A \ S) ∪ (A ∩ S) = A := by
      ext p
      simp only [mem_union, mem_sdiff, mem_inter]
      tauto
    rw [← sum_union disj, un]
  have total : (∑ p ∈ A, w p) = (∑ p ∈ A, 2*J/(p^2)) + A.card := by
    simp [w, sum_add_distrib]
  have score : (∑ p ∈ A \ S, w p) =
      A.card + (∑ p ∈ A, 2*J/(p^2)) - (∑ p ∈ A ∩ S, w p) := by
    rw [Nat.add_comm A.card, ← total, ← partition, Nat.add_sub_cancel]
  change ((∑ p ∈ A \ S, w p : ℕ) : ℚ) + _ < _
  rw [score]
  exact hmargin

end OMA.R_oeis_a085265_R2_H2_R1_H1_R1_H1_R3

import Mathlib

/-!
# The first prime-factor conjecture for OEIS A300984

Michel Lagneau posed the conjecture in 2018. This file proves its factorization
claim, both exponent bounds, the congruence modulo 12, and the minimum 676.
The other conjecture in the same entry concerns a majority of represented primes.

Proof developed by Codex for @dwilfand-sys. The squarefree-divisor product
calculation follows the argument used by @anmolspace in open-math-agents #9203.
Source: https://oeis.org/A300984

The five axiom reports at the end were checked in the Lean web editor using
Lean 4.37.0-rc1 and Mathlib on 27 November 2026.
-/

namespace Lagneau
open Finset
def squarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

def nonsquarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ Squarefree d, d

def PrimeShape : Prop := ∀ n : ℕ, 0 < n → Squarefree (squarefreeSum n) →
    Squarefree (nonsquarefreeSum n) →
    ∃ p i j : ℕ, p.Prime ∧ n = 2^i * p^j

private theorem sum_formula (n : ℕ) (hn : n ≠ 0) :
    squarefreeSum n = ∏ p ∈ n.primeFactors, (1+p) := by
  rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  change ∑ s ∈ n.primeFactors.powerset, s.val.prod = _
  rw [Finset.prod_one_add]
  exact Finset.sum_congr rfl fun s _ ↦ Finset.prod_val s

private theorem unique_odd {n p q : ℕ} (hn : n ≠ 0) (hs : Squarefree (squarefreeSum n))
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    p = q := by
  by_contra neq
  have dp : 2 ∣ 1+p := by
    have h := (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd.resolve_left hp2
    omega
  have dq : 2 ∣ 1+q := by
    have h := (Nat.prime_of_mem_primeFactors hq).eq_two_or_odd.resolve_left hq2
    omega
  have hq' := Finset.mem_erase.mpr ⟨Ne.symm neq, hq⟩
  apply (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two
  rw [sum_formula n hn, ← Finset.mul_prod_erase _ (fun x : ℕ ↦ 1+x) hp,
    ← Finset.mul_prod_erase _ (fun x : ℕ ↦ 1+x) hq', ← Nat.mul_assoc]
  exact dvd_mul_of_dvd_left (mul_dvd_mul dp dq) _

theorem lagneau_support : PrimeShape := by
  intro n hn hs _
  have hn0 := Nat.ne_of_gt hn
  have support : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n.primeFactors ⊆ {2,p} := by
    by_cases h : ∃ q ∈ n.primeFactors, q ≠ 2
    · obtain ⟨p, hp, hp2⟩ := h
      refine ⟨p, Nat.prime_of_mem_primeFactors hp, hp2, ?_⟩
      intro q hq
      by_cases hq2 : q = 2
      · simp [hq2]
      · simp [unique_odd hn0 hs hq hp hq2 hp2]
    · refine ⟨3, by decide, by decide, ?_⟩
      intro q hq
      have : q = 2 := by by_contra ne; exact h ⟨q,hq,ne⟩
      simp [this]
  obtain ⟨p, hp, hp2, hsub⟩ := support
  refine ⟨p, n.factorization 2, n.factorization p, hp, ?_⟩
  calc
    n = ∏ q ∈ n.primeFactors, q ^ n.factorization q := Nat.prod_primeFactors_pow_factorization hn0
    _ = ∏ q ∈ ({2, p} : Finset ℕ), q ^ n.factorization q := by
      apply Finset.prod_subset hsub
      intro q _ hq
      have hz : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
      simp [hz]
    _ = _ := by simp [Ne.symm hp2]
private theorem another_prime_square {n q : ℕ} (hq : q.Prime)
    (ht : Squarefree (nonsquarefreeSum n)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p*p ∣ n := by
  by_contra no
  apply Nat.squarefree_iff_prime_squarefree.mp ht q hq
  unfold nonsquarefreeSum
  apply Finset.dvd_sum
  intro d hd
  obtain ⟨hdiv, hbad⟩ := Finset.mem_filter.mp hd
  rw [Nat.squarefree_iff_prime_squarefree] at hbad
  push_neg at hbad
  obtain ⟨p, hp, hpd⟩ := hbad
  by_cases eq : p = q
  · simpa [eq] using hpd
  · exact False.elim (no ⟨p, hp, eq, hpd.trans (Nat.dvd_of_mem_divisors hdiv)⟩)

theorem lagneau_prime_shape {n : ℕ} (hn : n ≠ 0)
    (hs : Squarefree (squarefreeSum n)) (ht : Squarefree (nonsquarefreeSum n)) :
    ∃ p : ℕ, p.Prime ∧ p % 12 = 1 ∧ 4 ∣ n ∧ p*p ∣ n ∧ n.primeFactors = {2, p} := by
  obtain ⟨p,hp,hp2,hp_sq⟩ := another_prime_square Nat.prime_two ht
  have pm : p ∈ n.primeFactors := hp.mem_primeFactors ((dvd_mul_right p p).trans hp_sq) hn
  obtain ⟨q,hq,hqp,hq_sq⟩ := another_prime_square hp ht
  have qm : q ∈ n.primeFactors := hq.mem_primeFactors ((dvd_mul_right q q).trans hq_sq) hn
  have q2 : q = 2 := by
    by_contra h
    exact hqp (unique_odd hn hs qm pm h hp2)
  subst q
  have members : n.primeFactors = {2,p} := by
    ext y
    constructor
    · intro hy
      by_cases y2 : y = 2
      · simp [y2]
      · simp [unique_odd hn hs hy pm y2 hp2]
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> assumption
  have hsval : squarefreeSum n = 3*(1+p) := by
    rw [sum_formula n hn, members]
    simp [Ne.symm hp2]
  rw [hsval] at hs
  have no4 := Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
  have no9 := Nat.squarefree_iff_prime_squarefree.mp hs 3 (by decide)
  have p3 : p ≠ 3 := by
    rintro rfl
    exact no4 (by decide)
  have mod2 := hp.eq_two_or_odd.resolve_left hp2
  have mod3 : ¬ 3 ∣ p := by
    intro hd
    rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  refine ⟨p,hp,?_,hq_sq,hp_sq,members⟩
  have hd := Nat.div_add_mod p 12
  have hr := Nat.mod_lt p (by decide : 0 < 12)
  generalize he : p % 12 = r at *
  interval_cases r <;> omega

theorem lagneau_exponents {n : ℕ} (hn : n ≠ 0)
    (hs : Squarefree (squarefreeSum n)) (ht : Squarefree (nonsquarefreeSum n)) :
    ∃ p i j : ℕ, p.Prime ∧ p % 12 = 1 ∧ 2 ≤ i ∧ 2 ≤ j ∧ n = 2^i * p^j := by
  obtain ⟨p,hp,hr,h4,hp2,hf⟩ := lagneau_prime_shape hn hs ht
  have hne : 2 ≠ p := by omega
  refine ⟨p,n.factorization 2,n.factorization p,hp,hr,
    (Nat.prime_two.pow_dvd_iff_le_factorization hn).mp h4,
    (hp.pow_dvd_iff_le_factorization hn).mp (by simpa [pow_two] using hp2),?_⟩
  calc
    n = ∏ q ∈ n.primeFactors, q ^ n.factorization q := Nat.prod_primeFactors_pow_factorization hn
    _ = _ := by rw [hf]; simp [hne]

theorem lagneau_lower_bound {n : ℕ} (hn : n ≠ 0)
    (hs : Squarefree (squarefreeSum n)) (ht : Squarefree (nonsquarefreeSum n)) : 676 ≤ n := by
  obtain ⟨p,i,j,hp,hr,hi,hj,rfl⟩ := lagneau_exponents hn hs ht
  have h13 : 13 ≤ p := by have := hp.two_le; omega
  calc
    676 = 2^2 * 13^2 := by decide
    _ ≤ 2^i * p^j := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hi)
      ((Nat.pow_le_pow_left h13 2).trans (Nat.pow_le_pow_right hp.pos hj))

theorem lagneau_first_member : Squarefree (squarefreeSum 676) ∧ Squarefree (nonsquarefreeSum 676) := by
  have h0 : (676:ℕ) ≠ 0 := by decide
  have hf : (676:ℕ).primeFactorsList = [2,2,13,13] := by
    symm
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (by decide) (Nat.primeFactorsList_sorted 676).pairwise
    apply Nat.primeFactorsList_unique (by decide)
    norm_num [List.forall_mem_cons]
  have hs : squarefreeSum 676 = 42 := by
    rw [sum_formula 676 h0, ← Nat.toFinset_factors, hf]
    decide
  have ht : ∑ d ∈ (676:ℕ).divisors, d = 1281 := by
    rw [Nat.sum_divisors h0]
    simp only [← Nat.primeFactorsList_count_eq, ← Nat.toFinset_factors, hf]
    decide
  have split : squarefreeSum 676 + nonsquarefreeSum 676 = ∑ d ∈ (676:ℕ).divisors, d :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hns : nonsquarefreeSum 676 = 1239 := by omega
  rw [hs, hns]
  constructor <;> rw [Nat.squarefree_iff_prime_squarefree] <;> intro p hp hd
  all_goals have le := Nat.le_of_dvd (by decide) hd
  all_goals have pbound : p ≤ 35 := by nlinarith
  all_goals interval_cases p <;> norm_num at *

theorem lagneau_minimum : IsLeast {n : ℕ | 0 < n ∧ Squarefree (squarefreeSum n) ∧ Squarefree (nonsquarefreeSum n)} 676 := by
  refine ⟨⟨by decide, lagneau_first_member⟩,?_⟩
  intro n hn
  exact lagneau_lower_bound hn.1.ne' hn.2.1 hn.2.2

#print axioms lagneau_minimum
#print axioms lagneau_lower_bound
#print axioms lagneau_exponents
#print axioms lagneau_support
#print axioms lagneau_prime_shape
end Lagneau

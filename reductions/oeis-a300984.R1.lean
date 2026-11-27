import OMAStatements.S_oeis_a300984

/-!
The following argument settles the prime-support part of A300984.
Source: https://oeis.org/A300984
Credit: @dwilfand-sys. The product formula for the squarefree-divisor
sum is also used by @anmolspace in open-math-agents #9203.
-/

open Finset OMA.S_oeis_a300984

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

theorem lagneau_support : OMA.S_oeis_a300984.PrimeShape := by
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

namespace OMA.R_oeis_a300984_R1

open OMA.S_oeis_a300984

/-- Evaluate both divisor sums using the two exponents. -/
def H1 : Prop := ∀ p i j : ℕ, p.Prime → p ≠ 2 → 0<j →
  let S := (if i=0 then 1 else 3)*(1+p)
  let T := (∑ a ∈ Finset.range (i+1), 2^a) * (∑ b ∈ Finset.range (j+1), p^b)
  squarefreeSum (2^i*p^j) = S ∧ nonsquarefreeSum (2^i*p^j) = T-S

/-- Count represented odd primes using explicit geometric sums. -/
def H2 : Prop := by
  classical
  let F (B : ℕ) : Finset ℕ := (Finset.range (B+1)).filter fun p ↦ p.Prime ∧ p ≠ 2 ∧
      ∃ i j : ℕ, 0<j ∧ 2^i*p^j ≤ B ∧
        Squarefree ((if i=0 then 1 else 3)*(1+p)) ∧
        Squarefree ((∑ a ∈ Finset.range (i+1), 2^a) * (∑ b ∈ Finset.range (j+1), p^b) - (if i=0 then 1 else 3)*(1+p))
  exact ∀ m : ℕ, 7<m → (F (10^m)).card < 2*((F (10^m)).filter isA082539).card

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a300984.main := by
  classical
  intro h₁ h₂
  refine ⟨lagneau_support, ?_⟩
  let F (B : ℕ) : Finset ℕ := (Finset.range (B+1)).filter fun p ↦ p.Prime ∧ p ≠ 2 ∧
      ∃ i j : ℕ, 0<j ∧ 2^i*p^j ≤ B ∧
        Squarefree ((if i=0 then 1 else 3)*(1+p)) ∧
        Squarefree ((∑ a ∈ Finset.range (i+1), 2^a) * (∑ b ∈ Finset.range (j+1), p^b) - (if i=0 then 1 else 3)*(1+p))
  have same (B : ℕ) : representedPrimes B = F B := by
    ext p
    simp only [representedPrimes, F, Finset.mem_filter]
    constructor
    · rintro ⟨hm,hp,hp2,n,hn,hB,hs,ht,i,j,hj,rfl⟩
      obtain ⟨hS,hT⟩ := h₁ p i j hp hp2 hj
      exact ⟨hm,hp,hp2,i,j,hj,hB,hS ▸ hs,hT ▸ ht⟩
    · rintro ⟨hm,hp,hp2,i,j,hj,hB,hs,ht⟩
      obtain ⟨hS,hT⟩ := h₁ p i j hp hp2 hj
      exact ⟨hm,hp,hp2,2^i*p^j,Nat.mul_pos (pow_pos (by decide) i) (pow_pos hp.pos j),
        hB,hS.symm ▸ hs,hT.symm ▸ ht,i,j,hj,rfl⟩
  intro m hm
  change (representedPrimes (10^m)).card < 2*((representedPrimes (10^m)).filter isA082539).card
  rw [same]
  exact h₂ m hm

end OMA.R_oeis_a300984_R1

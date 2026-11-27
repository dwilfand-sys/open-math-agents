import OMAStatements.S_oeis_a300984

/-!
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

theorem OMA.solution : type_of% @OMA.S_oeis_a300984.main := by
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

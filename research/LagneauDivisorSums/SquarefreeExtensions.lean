import OMAStatements.S_oeis_a318807

/-!
Squarefree coprime multipliers preserve the ratio of the nonsquarefree and
squarefree divisor sums. The final lemma gives arbitrarily large integers
with the same ratio as any positive starting example. This is a research
draft pending a Lean kernel check. The squarefree divisor product is the
argument used by @anmolspace in open-math-agents PR 9203.
-/

open Finset OMA.S_oeis_a318807

namespace LagneauExtensions

private theorem squarefree_product (n : ℕ) (hn : n ≠ 0) :
    squarefreeSum n = ∏ p ∈ n.primeFactors, (1 + p) := by
  rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
  change ∑ s ∈ n.primeFactors.powerset, s.val.prod = _
  rw [Finset.prod_one_add]
  exact Finset.sum_congr rfl fun s _ ↦ Finset.prod_val s

private theorem split_sum (n : ℕ) :
    squarefreeSum n + nonsquarefreeSum n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

theorem squarefree_extension {n u : ℕ} (hn : n ≠ 0) (hu : u ≠ 0)
    (hc : n.Coprime u) (hfree : Squarefree u) :
    squarefreeSum (n * u) = squarefreeSum n * ArithmeticFunction.sigma 1 u ∧
    nonsquarefreeSum (n * u) = nonsquarefreeSum n * ArithmeticFunction.sigma 1 u := by
  have hall : ∀ d ∈ u.divisors, Squarefree d :=
    fun d hd ↦ hfree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  have hsum : squarefreeSum u = ArithmeticFunction.sigma 1 u := by
    rw [squarefreeSum, Finset.filter_eq_self.mpr hall, ArithmeticFunction.sigma_one_apply]
  have hprod : squarefreeSum (n * u) = squarefreeSum n * squarefreeSum u := by
    rw [squarefree_product _ (mul_ne_zero hn hu), squarefree_product n hn,
      squarefree_product u hu, Nat.primeFactors_mul hn hu, Finset.prod_union hc.disjoint_primeFactors]
  have hs := hprod.trans (congrArg (squarefreeSum n * ·) hsum)
  have htot : squarefreeSum (n * u) + nonsquarefreeSum (n * u) =
      squarefreeSum (n * u) + nonsquarefreeSum n * ArithmeticFunction.sigma 1 u := by
    calc
      squarefreeSum (n * u) + nonsquarefreeSum (n * u)
          = ArithmeticFunction.sigma 1 (n * u) := split_sum _
      _ = ArithmeticFunction.sigma 1 n * ArithmeticFunction.sigma 1 u :=
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc
      _ = squarefreeSum (n * u) + nonsquarefreeSum n * ArithmeticFunction.sigma 1 u := by
        rw [← split_sum n, Nat.add_mul, hs]
  exact ⟨hs, Nat.add_left_cancel htot⟩

theorem unbounded_fixed_ratio {b r : ℕ} (hb : 0 < b)
    (hbase : nonsquarefreeSum b = squarefreeSum b * r) (N : ℕ) :
    ∃ n > N, nonsquarefreeSum n = squarefreeSum n * r := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N b + 1)
  have hlarge : N < p := lt_of_le_of_lt (le_max_left N b) (by omega)
  have hlarge' : b < p := lt_of_le_of_lt (le_max_right N b) (by omega)
  have hndvd : ¬ p ∣ b := fun hd ↦ (not_le_of_gt hlarge') (Nat.le_of_dvd hb hd)
  have hc : b.Coprime p := (hprime.coprime_iff_not_dvd.mpr hndvd).symm
  obtain ⟨hs, ht⟩ := squarefree_extension hb.ne' hprime.ne_zero hc hprime.squarefree
  have hsize : p ≤ b * p := by simpa using Nat.mul_le_mul_right p hb
  refine ⟨b * p, lt_of_lt_of_le hlarge hsize, ?_⟩
  rw [ht, hs, hbase]
  ring

end LagneauExtensions

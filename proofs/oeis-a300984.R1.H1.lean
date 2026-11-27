import OMAReductions.R_oeis_a300984_R1

/-!
The two sums for a number of the form 2^i p^j. The squarefree divisor
sum is the product of one plus each distinct prime, as in @anmolspace's
proof in #9203. The full divisor sum is multiplicative on the two powers.
Source: https://oeis.org/A300984
Credit: @dwilfand-sys
-/

open Finset OMA.S_oeis_a300984 OMA.R_oeis_a300984_R1

theorem OMA.solution : OMA.R_oeis_a300984_R1.H1 := by
  intro p i j hp hp2 hj
  have hp0 := pow_ne_zero j hp.ne_zero
  have htwo := pow_ne_zero i (by decide : (2 : ℕ) ≠ 0)
  have hn := mul_ne_zero htwo hp0
  have hsf : squarefreeSum (2^i*p^j) = (if i=0 then 1 else 3)*(1+p) := by
    rw [squarefreeSum, Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq]
    change ∑ s ∈ (2^i*p^j).primeFactors.powerset, s.val.prod = _
    calc
      _ = ∏ q ∈ (2^i*p^j).primeFactors, (1+q) := by
        rw [Finset.prod_one_add]
        exact Finset.sum_congr rfl fun s _ ↦ Finset.prod_val s
      _ = _ := by
        by_cases hi : i=0
        · subst i
          simp [Nat.primeFactors_prime_pow hj.ne' hp]
        · rw [Nat.primeFactors_mul htwo hp0, Nat.primeFactors_prime_pow hi Nat.prime_two,
            Nat.primeFactors_prime_pow hj.ne' hp]
          simp [hi, Ne.symm hp2]
  have co : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have total : ∑ d ∈ (2^i*p^j).divisors, d =
      (∑ a ∈ Finset.range (i+1), 2^a) * (∑ b ∈ Finset.range (j+1), p^b) := by
    rw [(co.pow i j).sum_divisors_mul, Nat.sum_divisors_prime_pow Nat.prime_two,
      Nat.sum_divisors_prime_pow hp]
  have split : squarefreeSum (2^i*p^j) + nonsquarefreeSum (2^i*p^j) =
      ∑ d ∈ (2^i*p^j).divisors, d := Finset.sum_filter_add_sum_filter_not _ _ _
  refine ⟨hsf, ?_⟩
  omega

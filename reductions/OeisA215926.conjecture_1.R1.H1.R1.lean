import OMAReductions.R_OeisA215926_conjecture_1_R1

/-!
An odd almost perfect number has odd divisor sum, so all its prime exponents
are even. It therefore suffices to study odd squares. The first step isolates
at most three distinct prime factors, for which explicit divisor-ratio
bounds rule out almost perfection. The second step is the residual question.
-/

namespace OMA.OddAlmost

open scoped ArithmeticFunction.sigma
open ArithmeticFunction Finset

private theorem geometric_mod_two {p : ℕ} (hp : Odd p) (k : ℕ) :
    (∑ j ∈ range k, p ^ j) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp' : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
    rw [sum_range_succ, Nat.add_mod, ih, hp']
    omega

/-- For odd n, oddness of its divisor sum forces every prime exponent to be even. -/
theorem factorization_even_of_odd_sigma {n p : ℕ} (hn : 0 < n) (ho : Odd n)
    (hs : Odd (σ 1 n)) (hp : p ∈ n.primeFactors) : Even (n.factorization p) := by
  have pOdd : Odd p := by
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors hp
    rw [hc] at ho
    exact (Nat.odd_mul.mp ho).1
  let f (q : ℕ) := ∑ i ∈ range (n.factorization q + 1), q ^ i
  have prod : σ 1 n = ∏ q ∈ n.primeFactors, f q := by
    simpa only [mul_one, f] using
      (sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn.ne')
  obtain ⟨b, hb⟩ := dvd_prod_of_mem f hp
  rw [prod, hb] at hs
  have hgeom : f p % 2 = 1 := Nat.odd_iff.mp (Nat.odd_mul.mp hs).1
  have hpar := geometric_mod_two pOdd (n.factorization p + 1)
  change (∑ j ∈ range (n.factorization p + 1), p ^ j) % 2 = 1 at hgeom
  exact ⟨n.factorization p / 2, by omega⟩

theorem square_of_odd_sigma {n : ℕ} (hn : 0 < n) (ho : Odd n) (hs : Odd (σ 1 n)) :
    IsSquare n := by
  let root := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  refine ⟨root, ?_⟩
  change n = (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)) *
    (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2))
  rw [← Finset.prod_mul_distrib]
  refine (Nat.prod_primeFactors_pow_factorization hn.ne').trans (Finset.prod_congr rfl ?_)
  intro p hp
  obtain ⟨e, he⟩ := factorization_even_of_odd_sigma hn ho hs hp
  rw [← pow_add]
  congr 1
  omega

end OMA.OddAlmost

namespace OMA.R_OeisA215926_conjecture_1_R1_H1_R1

open scoped ArithmeticFunction.sigma

/-- No nontrivial odd square with at most three distinct prime divisors is almost perfect. -/
def H1 : Prop := ∀ m : ℕ, Odd m → 1 < m ^ 2 → m.primeFactors.card ≤ 3 →
    1 + σ 1 (m ^ 2) ≠ 2 * m ^ 2

/-- Exclude odd squares with at least four distinct prime divisors. -/
def H2 : Prop := ∀ m : ℕ, Odd m → 4 ≤ m.primeFactors.card →
    1 + σ 1 (m ^ 2) ≠ 2 * m ^ 2

theorem main : H1 → H2 → OMA.R_OeisA215926_conjecture_1_R1.H1 := by
  intro hfew hmany n ho he
  by_contra hn
  have hn' : 1 < n := by obtain ⟨t, ht⟩ := ho; omega
  have hos : Odd (σ 1 n) := ⟨n - 1, by omega⟩
  obtain ⟨m, hm⟩ := OMA.OddAlmost.square_of_odd_sigma (by omega : 0 < n) ho hos
  have hsq : n = m ^ 2 := by simpa [pow_two] using hm
  rw [hm] at ho
  rw [hsq] at hn' he
  have hmo := (Nat.odd_mul.mp ho).1
  by_cases h : m.primeFactors.card ≤ 3
  · exact hfew m hmo hn' h he
  · exact hmany m hmo (by omega) he

end OMA.R_OeisA215926_conjecture_1_R1_H1_R1

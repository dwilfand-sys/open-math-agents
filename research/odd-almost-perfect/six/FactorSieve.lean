import Mathlib

namespace OMA.AlmostPerfectFactorSieve

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- Every prime dividing the divisor sum of an almost-perfect square is
congruent to one or minus one modulo eight. -/
theorem divisor_sum_prime_classes {n q : ℕ} (hs : IsSquare n)
    (he : 1 + σ 1 n = 2 * n) (hq : q.Prime) (hd : q ∣ σ 1 n) :
    q % 8 = 1 ∨ q % 8 = 7 := by
  letI : Fact q.Prime := ⟨hq⟩
  have ho : Odd (σ 1 n) := ⟨n-1, by omega⟩
  have hne : q ≠ 2 := by rintro rfl; exact ho.not_two_dvd_nat hd
  apply (ZMod.exists_sq_eq_two_iff hne).mp
  obtain ⟨r, hr⟩ := hs
  have hz := (ZMod.natCast_eq_zero_iff (σ 1 n) q).mpr hd
  have hh := congrArg (fun a : ℕ => (a : ZMod q)) he
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, hz, add_zero] at hh
  have hx : (1 : ZMod q) = 2 * ((r : ZMod q) * r) := by
    rw [hr, Nat.cast_mul] at hh
    exact hh
  refine ⟨2*(r : ZMod q), ?_⟩
  calc
    (2 : ZMod q) = 2 * 1 := by ring
    _ = 2 * (2 * ((r : ZMod q) * r)) := by rw [← hx]
    _ = (2 * (r : ZMod q)) * (2 * (r : ZMod q)) := by ring

/-- Apply the prime residue condition to any individual prime-power term in
the multiplicative divisor-sum formula. -/
theorem geometric_factor_sieve {n p q : ℕ} (hn : 0 < n) (hs : IsSquare n)
    (he : 1 + σ 1 n = 2 * n) (hp : p ∈ n.primeFactors) (hq : q.Prime)
    (hd : q ∣ ∑ i ∈ range (n.factorization p+1), p^i) : q % 8 = 1 ∨ q % 8 = 7 := by
  apply divisor_sum_prime_classes hs he hq
  apply hd.trans
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne']
  simp only [mul_one]
  exact dvd_prod_of_mem (fun r => ∑ i ∈ range (n.factorization r+1), r^i) hp

private theorem product_classes (xs : List ℕ)
    (h : ∀ x ∈ xs, x%8 = 1 ∨ x%8 = 7) : xs.prod%8 = 1 ∨ xs.prod%8 = 7 := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    rw [List.prod_cons, Nat.mul_mod]
    rcases hx with hx | hx <;> rcases ht with ht | ht <;> rw [hx, ht] <;> decide

/-- The geometric sum itself is one or minus one modulo eight. -/
theorem geometric_sum_class {n p : ℕ} (hn : 0 < n) (hs : IsSquare n)
    (he : 1 + σ 1 n = 2 * n) (hp : p ∈ n.primeFactors) :
    let t := ∑ i ∈ range (n.factorization p+1), p^i
    t % 8 = 1 ∨ t % 8 = 7 := by
  let t := ∑ i ∈ range (n.factorization p+1), p^i
  change t%8 = 1 ∨ t%8 = 7
  have hterm : p^0 ≤ t :=
    single_le_sum (fun i _ => Nat.zero_le (p^i)) (mem_range.mpr (by omega))
  have ht : t ≠ 0 := by simpa using (show 0 < t by simpa using hterm).ne'
  have h := product_classes t.primeFactorsList (fun q hq =>
    geometric_factor_sieve hn hs he hp (Nat.prime_of_mem_primeFactorsList hq)
      (Nat.dvd_of_mem_primeFactorsList hq))
  simpa [Nat.prod_primeFactorsList ht] using h

private theorem geometric_mod_eight (p : ℕ) (ho : Odd p) (k : ℕ) :
    (∑ i ∈ range (2*k+1), p^i) ≡ 1+k*(p+1) [MOD 8] := by
  have hodd := Nat.odd_iff.mp ho
  have hsq : p^2 ≡ 1 [MOD 8] := by
    change (p^2)%8 = 1
    rw [pow_two, Nat.mul_mod]
    have hc : p%8=1 ∨ p%8=3 ∨ p%8=5 ∨ p%8=7 := by omega
    rcases hc with h | h | h | h <;> rw [h] <;> decide
  have even_pow (u : ℕ) : p^(2*u) ≡ 1 [MOD 8] := by
    simpa [pow_mul] using (Nat.ModEq.pow u hsq)
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    rw [show 2*(k+1)+1 = 2*k+1+1+1 by omega, sum_range_succ, sum_range_succ]
    have hoddpow : p^(2*k+1) ≡ p [MOD 8] := by
      rw [pow_succ]
      simpa using ((even_pow k).mul (show p ≡ p [MOD 8] from rfl))
    have hevenpow : p^(2*k+1+1) ≡ 1 [MOD 8] := by
      rw [show 2*k+1+1=2*(k+1) by omega]
      exact even_pow (k+1)
    calc
      _ ≡ (1+k*(p+1))+p+1 [MOD 8] := (ih.add hoddpow).add hevenpow
      _ = 1+(k+1)*(p+1) := by ring

/-- Compatible residue classes for an odd prime and its even exponent. -/
def allowed (a b : ℕ) : Prop :=
  (a=1 ∧ (b=0 ∨ b=6)) ∨ (a=3 ∧ (b=0 ∨ b=4)) ∨
  (a=5 ∧ (b=0 ∨ b=2)) ∨ (a=7 ∧ (b=0 ∨ b=2 ∨ b=4 ∨ b=6))

theorem exponent_classes {n p : ℕ} (hn : 0 < n) (hs : IsSquare n)
    (he : 1 + σ 1 n = 2 * n) (hp : p ∈ n.primeFactors) (ho : Odd p) :
    allowed (p%8) (n.factorization p%8) := by
  obtain ⟨k, hk⟩ := Nat.isSquare_iff_even_factorization.mp hs p (Nat.prime_of_mem_primeFactors hp)
  have hExp : n.factorization p = 2*k := by omega
  have hlocal := geometric_sum_class hn hs he hp
  change (∑ i ∈ range (n.factorization p+1), p^i)%8=1 ∨
    (∑ i ∈ range (n.factorization p+1), p^i)%8=7 at hlocal
  rw [hExp] at hlocal ⊢
  have hm := geometric_mod_eight p ho k
  have hk' : k ≡ k%8 [MOD 8] := by simp [Nat.ModEq]
  have hp' : p ≡ p%8 [MOD 8] := by simp [Nat.ModEq]
  have ho' : 1 ≡ 1 [MOD 8] := rfl
  have hm' := hm.trans (ho'.add (hk'.mul (hp'.add ho')))
  have ht : (2*k)%8 = (2*(k%8))%8 := (show 2 ≡ 2 [MOD 8] from rfl).mul hk'
  rw [show (∑ i ∈ range (2*k+1), p^i)%8 = (1+(k%8)*(p%8+1))%8 from hm'] at hlocal
  rw [ht]
  have cert : ∀ a b : Fin 8, a.val%2=1 →
      ((1+b.val*(a.val+1))%8=1 ∨ (1+b.val*(a.val+1))%8=7) →
        (a.val=1 ∧ ((2*b.val)%8=0 ∨ (2*b.val)%8=6)) ∨
        (a.val=3 ∧ ((2*b.val)%8=0 ∨ (2*b.val)%8=4)) ∨
        (a.val=5 ∧ ((2*b.val)%8=0 ∨ (2*b.val)%8=2)) ∨
        (a.val=7 ∧ ((2*b.val)%8=0 ∨ (2*b.val)%8=2 ∨ (2*b.val)%8=4 ∨ (2*b.val)%8=6)) := by decide
  have hodd := Nat.odd_iff.mp ho
  exact cert ⟨p%8, by omega⟩ ⟨k%8, by omega⟩ (by omega) hlocal

end OMA.AlmostPerfectFactorSieve

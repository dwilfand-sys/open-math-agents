import Mathlib

/-!
# OEIS A394399 and the shape of a twin-prime average

Source: https://oeis.org/A394399
Credit: @dwilfand-sys (Lean formalization by Codex). Aied Sulaiman posed
the conjecture on April 24, 2026. The neighboring primes are k-1 and k+1.
ArithmeticFunction.sigma 1 is the ordinary sum of positive divisors.
-/

namespace OMA.S_oeis_a394399

theorem main : ∀ k : ℕ, (k - 1).Prime → (k + 1).Prime →
    Nat.gcd k (ArithmeticFunction.sigma 1 k) = 3 →
    ∃ m : ℕ, k = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a394399

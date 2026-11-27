import Mathlib

/-!
# A400795 candidate representations from divisors of `n + 1`

The positive lattice-point counts in OEIS A400795 use side lengths greater
than one. An odd prime divisor gives an even first side and an odd second
side. The numerical equivalence itself works for every proper divisor `q > 2`.

Source: https://oeis.org/A400795
Research formalization: Codex for @dwilfand-sys.
-/

namespace A400795Witness

def triangleCount (a b : ℕ) : ℕ :=
  (a * b + a + b - Nat.gcd a b) / 2

theorem factor_witness {n q m : ℕ} (hq : 2 < q) (hm : 1 < m)
    (hn : n + 1 = q * m) :
    1 < q - 1 ∧ 1 < 2 * m - 1 ∧
      (triangleCount (q - 1) (2 * m - 1) = n ↔ (q - 1).Coprime (2 * n + 1)) := by
  let a := q - 1
  let b := 2 * m - 1
  have ha : a + 1 = q := by dsimp [a]; omega
  have hb : b + 1 = 2 * m := by dsimp [b]; omega
  have haq : 1 < a := by omega
  have hbm : 1 < b := by omega
  have hqn : q ≤ n + 1 := by
    rw [hn]
    simpa using Nat.mul_le_mul_left q (show 1 ≤ m by omega)
  have hnpos : 0 < n := by omega
  have hp : (a + 1) * (b + 1) = 2 * (n + 1) := by
    rw [ha, hb, hn]
    ring
  have hs : a * b + a + b = 2 * n + 1 := by nlinarith only [hp]
  have he : 2 * n + 1 = b + (b + 1) * a := by nlinarith only [hp]
  have hg : a.gcd (2 * n + 1) = a.gcd b := by
    rw [he, Nat.gcd_add_mul_right_right]
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (by omega)
  change 1 < a ∧ 1 < b ∧ (triangleCount a b = n ↔ a.Coprime (2 * n + 1))
  refine ⟨haq, hbm, ?_⟩
  change (a * b + a + b - a.gcd b) / 2 = n ↔ a.gcd (2 * n + 1) = 1
  rw [hs, hg]
  omega

theorem proper_divisor_witness {n q : ℕ} (hq : 2 < q) (hproper : q < n + 1)
    (hdiv : q ∣ n + 1) :
    1 < q - 1 ∧ 1 < 2 * ((n + 1) / q) - 1 ∧
      (triangleCount (q - 1) (2 * ((n + 1) / q) - 1) = n ↔
        (q - 1).Coprime (2 * n + 1)) := by
  let m := (n + 1) / q
  have hn : n + 1 = q * m := by
    dsimp [m]
    rw [Nat.mul_comm q, Nat.div_mul_cancel hdiv]
  have hm : 1 < m := by
    by_contra! h
    have hcases : m = 0 ∨ m = 1 := by omega
    rcases hcases with hz | ho
    · rw [hz, Nat.mul_zero] at hn
      omega
    · rw [ho, Nat.mul_one] at hn
      omega
  exact factor_witness hq hm hn

theorem odd_prime_witness {n q : ℕ} (hprime : q.Prime) (hodd : q ≠ 2)
    (hproper : q < n + 1) (hdiv : q ∣ n + 1) :
    1 < q - 1 ∧ 1 < 2 * ((n + 1) / q) - 1 ∧
      (triangleCount (q - 1) (2 * ((n + 1) / q) - 1) = n ↔
        (q - 1).Coprime (2 * n + 1)) := by
  have htwo := hprime.two_le
  exact proper_divisor_witness (by omega) hproper hdiv

end A400795Witness

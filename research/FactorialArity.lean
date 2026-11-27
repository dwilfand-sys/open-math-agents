import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-! Symmetric factorial ratios of arbitrary arity. The arity is written as
`k+1` to include the identity case without truncated subtraction. The cubic
and quartic specializations occur in Peter Bala's A361027 and A361032.
Unnormalized integrality is also a specialization of the sufficient condition
in Xin Chen and Jane Wang, §6.1.1, equation (10) and Remark 6.5:
https://www-users.cse.umn.edu/~reiner/REU/ChenWang2012.pdf .
The prime-power valuation then follows from Legendre's digit-sum formula. -/

namespace FactorialArity

theorem arity_floor (k a b q : ℕ) (hq : 0 < q) :
    k * ((a + b) / q) + a / q + b / q ≤ ((k+1)*a)/q + ((k+1)*b)/q := by
  have scale (x : ℕ) : (k+1) * (x/q) ≤ ((k+1)*x)/q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self x q)
  by_cases h : (a+b)/q ≤ a/q + b/q
  · calc
      k * ((a+b)/q) + a/q + b/q ≤ k * (a/q + b/q) + a/q + b/q := by
        exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left k h) _) _
      _ = (k+1) * (a/q) + (k+1) * (b/q) := by ring
      _ ≤ ((k+1)*a)/q + ((k+1)*b)/q := Nat.add_le_add (scale a) (scale b)
  · have upper (x : ℕ) : x < (x/q + 1)*q :=
      (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self _)
    have near : (k+1) * ((a+b)/q) ≤ ((k+1)*a)/q + ((k+1)*b)/q + 1 := by
      by_contra! fail
      have rev : (((k+1)*a)/q + ((k+1)*b)/q + 2)*q ≤ ((k+1)*((a+b)/q))*q :=
        Nat.mul_le_mul_right q (by omega)
      have lower := Nat.mul_le_mul_left (k+1) (Nat.div_mul_le_self (a+b) q)
      have ua := upper ((k+1)*a)
      have ub := upper ((k+1)*b)
      nlinarith only [rev, lower, ua, ub]
    rw [Nat.add_mul, Nat.one_mul] at near
    omega

/-- All symmetric factorial ratios with arity at least one are integers. -/
theorem arity_divisibility (k n s : ℕ) :
    n.factorial * s.factorial * (n+s).factorial ^ k ∣
      ((k+1)*n).factorial * ((k+1)*s).factorial := by
  have hns := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s)
  have hpow := pow_ne_zero k (Nat.factorial_ne_zero (n+s))
  apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero hns hpow)
    (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))).mp
  intro p hp
  let bound := (k+1)*(n+s)+1
  have expand (j : ℕ) (hj : j < bound) :
      j.factorial.factorization p = ∑ i ∈ Finset.Ico 1 bound, j / p^i :=
    Nat.factorization_factorial hp ((Nat.log_le_self p j).trans_lt hj)
  have mulVal (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a*b).factorization p = a.factorization p + b.factorization p := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  rw [mulVal _ _ hns hpow, mulVal _ _ (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s),
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    mulVal _ _ (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  have hsum : n+s ≤ (k+1)*(n+s) := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hn := Nat.mul_le_mul_left (k+1) (Nat.le_add_right n s)
  have hs := Nat.mul_le_mul_left (k+1) (Nat.le_add_left s n)
  rw [expand n (by dsimp [bound]; omega), expand s (by dsimp [bound]; omega),
      expand (n+s) (by dsimp [bound]; omega), expand ((k+1)*n) (by dsimp [bound]; omega),
      expand ((k+1)*s) (by dsimp [bound]; omega)]
  have h : (∑ i ∈ Finset.Ico 1 bound, (k*((n+s)/p^i) + n/p^i + s/p^i)) ≤
      ∑ i ∈ Finset.Ico 1 bound, (((k+1)*n)/p^i + ((k+1)*s)/p^i) :=
    Finset.sum_le_sum (fun i _ ↦ arity_floor k n s (p^i) (pow_pos hp.pos i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  omega

/-- The geometric sum `1 + p + ⋯ + p^(e−1)`, with value zero for `e=0`. -/
def geometric (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | e+1 => geometric p e + p^e

private theorem geometric_identity (p e : ℕ) (hp : 0 < p) :
    p^e = (p-1)*geometric p e + 1 := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
    rw [pow_succ, geometric, Nat.mul_add]
    have split : p = (p-1)+1 := by omega
    calc
      p^e*p = p^e*((p-1)+1) := congrArg (p^e * ·) split
      _ = (p-1)*p^e + p^e := by ring
      _ = (p-1)*geometric p e + (p-1)*p^e + 1 := by omega

private theorem scaled_factorial (p e t : ℕ) (hp : p.Prime) :
    (p^e*t).factorial.factorization p =
      t.factorial.factorization p + geometric p e * t := by
  induction e with
  | zero => simp [geometric]
  | succ e ih =>
    rw [show p^(e+1)*t = p*(p^e*t) by rw [pow_succ]; ring,
      Nat.factorization_factorial_mul hp, ih, geometric]
    ring

/-- At arity `p^e` the exact valuation is the base-`p` digit sum of
`n+s`, multiplied by the geometric sum. -/
theorem prime_power_valuation (p e n s : ℕ) (hp : p.Prime) :
    (((p^e*n).factorial * (p^e*s).factorial) /
      (n.factorial * s.factorial * (n+s).factorial ^ (p^e-1))).factorization p =
      geometric p e * (p.digits (n+s)).sum := by
  let k := p^e-1
  let d := n.factorial * s.factorial * (n+s).factorial^k
  let u := (p^e*n).factorial * (p^e*s).factorial
  let r := u/d
  have hpw := pow_pos hp.pos e
  have hk : k+1 = p^e := by dsimp [k]; omega
  have hgeo : k = (p-1)*geometric p e := by
    have h := geometric_identity p e hp.pos
    omega
  have hdiv : d ∣ u := by
    simpa only [hk, d, u] using arity_divisibility k n s
  have hns := mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s)
  have hpow := pow_ne_zero k (Nat.factorial_ne_zero (n+s))
  have hd : d ≠ 0 := mul_ne_zero hns hpow
  have hu : u ≠ 0 := mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have heq : r*d = u := Nat.div_mul_cancel hdiv
  have hr : r ≠ 0 := fun hz ↦ hu (by simpa [hz] using heq.symm)
  have mulVal (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      (a*b).factorization p = a.factorization p + b.factorization p := by
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have ht := (mulVal _ _ hr hd).symm.trans (congrArg (fun j : ℕ ↦ j.factorization p) heq)
  dsimp only [d, u] at ht
  rw [mulVal _ _ hns hpow, mulVal _ _ (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero s),
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    mulVal _ _ (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    scaled_factorial p e n hp, scaled_factorial p e s hp] at ht
  have digits := Nat.sub_one_mul_factorization_factorial (n := n+s) hp
  have hbound := Nat.digit_sum_le p (n+s)
  have sum : (p-1)*(n+s).factorial.factorization p + (p.digits (n+s)).sum = n+s := by omega
  have mult := congrArg (geometric p e * ·) sum
  rw [hgeo] at ht
  change r.factorization p = _
  nlinarith only [ht, mult]

end FactorialArity

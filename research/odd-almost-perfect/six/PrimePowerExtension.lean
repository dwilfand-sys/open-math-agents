import Mathlib

namespace OMA.AlmostPerfectExtension

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem extension_arithmetic {b s p e : ℕ} (hp : Odd p) (he : 0 < e)
    (hit : 1 + s * (∑ i ∈ range (e + 1), p ^ i) = 2 * (b * p ^ e)) :
    let d := 2*b-s
    2 ≤ d ∧ d*p < 2*b ∧ 2*b < d*(p+1) ∧ (2*b)/d = p ∧
      (2*b-d*p) * (∑ i ∈ range e, p ^ i) = d-1 := by
  let g := ∑ i ∈ range e, p ^ i
  let d := 2*b-s
  change 2 ≤ d ∧ d*p < 2*b ∧ 2*b < d*(p+1) ∧ (2*b)/d = p ∧ (2*b-d*p)*g = d-1
  have hterm : p ^ 0 ≤ g := single_le_sum (fun i _ => Nat.zero_le (p ^ i)) (mem_range.mpr he)
  have hg : 0 < g := by simpa using hterm
  have hstep : p*g + 1 = g + p ^ e := by
    change p * (∑ i ∈ range e, p ^ i) + 1 = (∑ i ∈ range e, p ^ i) + p ^ e
    calc
      _ = ∑ i ∈ range (e+1), p ^ i := by
        rw [sum_range_succ' (fun i => p ^ i) e]
        simp_rw [pow_succ]
        rw [← sum_mul, pow_zero, Nat.mul_comm]
      _ = _ := sum_range_succ _ e
  rw [sum_range_succ] at hit
  change 1 + s * (g + p ^ e) = 2 * (b * p ^ e) at hit
  have hs : s < 2*b := by
    by_contra! h
    have hm := Nat.mul_le_mul_right (p ^ e) h
    nlinarith only [hm, hit, Nat.zero_le (s*g)]
  have hds : d + s = 2*b := Nat.sub_add_cancel hs.le
  have hde : d * p ^ e = s*g + 1 := by
    have hd := congrArg (fun z : ℕ => z * p ^ e) hds
    nlinarith only [hd, hit]
  have bal : d*p*g + d = 2*b*g + 1 := by
    have ha := congrArg (fun z : ℕ => d*z) hstep
    have hb := congrArg (fun z : ℕ => z*g) hds
    nlinarith only [hde, ha, hb]
  have hd2 : 2 ≤ d := by
    by_contra! h
    have hd : d = 1 := by omega
    simp only [hd, one_mul] at bal
    have hpg : p*g = (2*b)*g := by omega
    have hpe := Nat.eq_of_mul_eq_mul_right hg hpg
    obtain ⟨t, ht⟩ := hp
    omega
  have lo : d*p < 2*b := by
    by_contra! h
    have hm := Nat.mul_le_mul_right g h
    omega
  have eq : (2*b-d*p)*g = d-1 := by
    rw [Nat.sub_mul]
    omega
  have hi : 2*b < d*(p+1) := by
    have hm := Nat.mul_le_mul_left (2*b-d*p) (show 1 ≤ g by omega)
    rw [Nat.mul_one] at hm
    rw [Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨hd2, lo, hi, Nat.div_eq_of_lt_le ?_ ?_, eq⟩
  · simpa [Nat.mul_comm] using lo.le
  · simpa [Nat.mul_comm] using hi

/-- The odd prime in a coprime prime-power extension of an almost-perfect
number is the integer part of twice the core divided by its deficiency. -/
theorem extension_prime {b p e : ℕ} (hp : p.Prime) (hodd : Odd p) (he : 0 < e)
    (hc : b.Coprime p) (hit : 1 + σ 1 (b * p ^ e) = 2 * (b * p ^ e)) :
    let d := 2*b - σ 1 b
    2 ≤ d ∧ d*p < 2*b ∧ 2*b < d*(p+1) ∧ (2*b)/d = p ∧
      (2*b-d*p) * (∑ i ∈ range e, p ^ i) = d-1 := by
  rw [isMultiplicative_sigma.map_mul_of_coprime (hc.pow_right e), sigma_one_apply_prime_pow hp] at hit
  exact extension_arithmetic hodd he hit

/-- A fixed core has at most one coprime odd prime-power extension that is almost perfect. -/
theorem unique_extension {b p q a c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hop : Odd p) (hoq : Odd q) (ha : 0 < a) (hc : 0 < c)
    (hbp : b.Coprime p) (hbq : b.Coprime q)
    (hA : 1 + σ 1 (b * p ^ a) = 2 * (b * p ^ a))
    (hC : 1 + σ 1 (b * q ^ c) = 2 * (b * q ^ c)) : p = q ∧ a = c := by
  obtain ⟨_, hlo, _, hpa, hgeom⟩ := extension_prime hp hop ha hbp hA
  obtain ⟨_, _, _, hqc, hgeom'⟩ := extension_prime hq hoq hc hbq hC
  have hpq : p = q := hpa.symm.trans hqc
  subst q
  refine ⟨rfl, ?_⟩
  have hmono : StrictMono (fun k : ℕ => ∑ i ∈ range k, p ^ i) :=
    strictMono_nat_of_lt_succ fun k => by
      change (∑ i ∈ range k, p ^ i) < ∑ i ∈ range (k + 1), p ^ i
      rw [sum_range_succ]
      have hpos := pow_pos hp.pos k
      omega
  apply hmono.injective
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hlo) (hgeom.trans hgeom'.symm)

end OMA.AlmostPerfectExtension

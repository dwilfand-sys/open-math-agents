import OMAReductions.R_oeis_a400795_R1
import Mathlib

/-!
Source: https://oeis.org/A400795
Credit: @dwilfand-sys
For a suitable prime q dividing n+1, set k=(n+1)/q. The pair q−1 and
2k−1 works because q(2k−1)+(q−1)=2n+1. The construction is from the
A400795 density manuscript at dwilfand-sys/open-math-agents.
-/

namespace A400795.PrimeWitness

theorem gives_pair (n q : ℕ) (hq : 2 < q) (hlt : q < n+1) (hd : q ∣ n+1)
    (hcop : Nat.Coprime (q-1) (2*n+1)) :
    1 < q-1 ∧ 1 < 2*((n+1)/q)-1 ∧
      OMA.S_oeis_a400795.triangleCount (q-1) (2*((n+1)/q)-1) = n := by
  let k := (n+1)/q
  let a := q-1
  let b := 2*k-1
  have hqk : q*k = n+1 := by
    simpa only [k, Nat.mul_comm q] using Nat.div_mul_cancel hd
  have hk : 1 < k := by
    by_contra! hk
    have hle := Nat.mul_le_mul_left q hk
    rw [Nat.mul_one] at hle
    omega
  have ha : a+1 = q := by dsimp [a]; omega
  have hb : b+1 = 2*k := by dsimp [b]; omega
  have hprod : (a+1)*(b+1) = 2*(n+1) := by
    rw [ha, hb, ← hqk]
    ring
  have hqb : q*b+q = 2*(n+1) := by
    calc
      q*b+q = q*(b+1) := by ring
      _ = (a+1)*(b+1) := by rw [ha]
      _ = 2*(n+1) := hprod
  have hsum : q*b+a = 2*n+1 := by omega
  have hga := Nat.gcd_dvd_left a b
  have hgb := Nat.gcd_dvd_right a b
  have hgn : a.gcd b ∣ 2*n+1 := by
    rw [← hsum]
    exact dvd_add (dvd_mul_of_dvd_right hgb q) hga
  have hgc : a.gcd (2*n+1) = 1 := hcop
  have hg1 : a.gcd b ∣ 1 := by simpa only [hgc] using (Nat.dvd_gcd hga hgn)
  have hg : a.gcd b = 1 := Nat.dvd_one.mp hg1
  change 1 < a ∧ 1 < b ∧ (a*b+a+b-a.gcd b)/2 = n
  refine ⟨by omega, by omega, ?_⟩
  have hpoly : a*b+a+b+1 = 2*(n+1) := by
    calc
      a*b+a+b+1 = (a+1)*(b+1) := by ring
      _ = 2*(n+1) := hprod
  rw [hg]
  omega

end A400795.PrimeWitness

theorem OMA.solution : OMA.R_oeis_a400795_R1.H3 := by
  intro n q _ hq hlt hd hcop
  exact A400795.PrimeWitness.gives_pair n q hq hlt hd hcop

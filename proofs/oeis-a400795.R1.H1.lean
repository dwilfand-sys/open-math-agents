import OMAReductions.R_oeis_a400795_R1
import Mathlib

/-!
Arithmetic obstruction for the strongly nontriangular numbers of Petersen,
Validashti and Wayland. On the candidate family n=2p−1, the prime and
roughness conditions rule out small gcds and give a bilinear factor equation.
Source: https://oeis.org/A400795
Credit: @dwilfand-sys
-/

namespace A400795.Obstruction

open OMA.S_oeis_a400795

private theorem numerator {a b n : ℕ} (ha : 1 < a)
    (ht : triangleCount a b = n) :
    2*n + a.gcd b = a*b+a+b := by
  have hle : a.gcd b ≤ a :=
    Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a b)
  have he : 2 ∣ a.gcd b ↔ 2 ∣ a ∧ 2 ∣ b := Nat.dvd_gcd_iff
  have hm := Nat.mul_mod a b 2
  have hpar : (a*b+a+b)%2 = a.gcd b%2 := by
    rcases Nat.mod_two_eq_zero_or_one a with ea | ea <;>
      rcases Nat.mod_two_eq_zero_or_one b with eb | eb <;>
      simp only [ea, eb] at hm <;> omega
  change (a*b+a+b-a.gcd b)/2 = n at ht
  omega

private theorem common_three {p a b : ℕ} (hp : p.Prime)
    (hr : p%3 = 1) (ha : 1 < a) (hb : 1 < b)
    (hfac : (a+1)*(b+1) = 4*p) (hdiv : p ∣ a+1) : 3 ∣ a.gcd b := by
  obtain ⟨k,hk⟩ := hdiv
  have hmul : p*((b+1)*k) = p*4 := by
    calc
      p*((b+1)*k) = (p*k)*(b+1) := by ring
      _ = (a+1)*(b+1) := by rw [← hk]
      _ = 4*p := hfac
      _ = p*4 := Nat.mul_comm _ _
  have hprod : (b+1)*k = 4 := Nat.eq_of_mul_eq_mul_left hp.pos hmul
  have hpos : k ≠ 0 := by
    intro hz
    rw [hz, Nat.mul_zero] at hprod
    omega
  have hkone : k = 1 := by
    by_contra hk'
    have h := Nat.mul_le_mul (by omega : 3 ≤ b+1) (by omega : 2 ≤ k)
    omega
  rw [hkone, Nat.mul_one] at hprod hk
  apply Nat.dvd_gcd <;> omega

/-- On the split-prime family, a putative representation has a large gcd
and yields the constrained bilinear equation counted by the switching proof. -/
theorem large_gcd {p a b y : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hmod : p%3 = 1)
    (hsplit : ∀ d : ℕ, d ∣ 4*p+1 → d%4 ≠ 3)
    (hrough : ∀ d : ℕ, 1 < d → d ≤ y → ¬ d ∣ 2*p-1)
    (ha : 1 < a) (hb : 1 < b) (ht : triangleCount a b = 2*p-1) :
    y < a.gcd b ∧ ∃ u v : ℕ, 0 < u ∧ 0 < v ∧
      2*(2*p-1) = (a.gcd b)^2*(u*v) + (a.gcd b)*(u+v-1) := by
  let g := a.gcd b
  have hnum : 2*(2*p-1)+g = a*b+a+b := numerator ha ht
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (by omega)
  have hfactor : (a+1)*(b+1) = 2*(2*p-1)+g+1 := by
    calc
      (a+1)*(b+1) = a*b+a+b+1 := by ring
      _ = _ := by omega
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  obtain ⟨u,hu⟩ := hga
  obtain ⟨v,hv⟩ := hgb
  have hup : 0 < u := by
    by_contra! hz
    have h0 : u=0 := by omega
    rw [h0,Nat.mul_zero] at hu
    omega
  have hvp : 0 < v := by
    by_contra! hz
    have h0 : v=0 := by omega
    rw [h0,Nat.mul_zero] at hv
    omega
  have hprod : a*b = g^2*(u*v) := by
    calc
      a*b = (g*u)*(g*v) := congrArg₂ (· * ·) hu hv
      _ = _ := by ring
  have hlin : g*(u+v-1)+g = a+b := by
    calc
      g*(u+v-1)+g = g*((u+v-1)+1) := by ring
      _ = g*(u+v) := by rw [show u+v-1+1=u+v by omega]
      _ = g*u+g*v := Nat.mul_add _ _ _
      _ = a+b := congrArg₂ (· + ·) hu.symm hv.symm
  have htable : 2*(2*p-1) = g^2*(u*v)+g*(u+v-1) := by omega
  refine ⟨?_,u,v,hup,hvp,htable⟩
  change y < g
  have hnot1 : g ≠ 1 := by
    intro h1
    have hfac : (a+1)*(b+1) = 4*p := by omega
    have hd : p ∣ (a+1)*(b+1) := ⟨4,by rw [hfac,Nat.mul_comm]⟩
    have h3 : 3 ∣ g := by
      rcases hp.dvd_mul.mp hd with h | h
      · exact common_three hp hmod ha hb hfac h
      · change 3 ∣ a.gcd b
        rw [Nat.gcd_comm]
        exact common_three hp hmod hb ha ((Nat.mul_comm _ _).trans hfac) h
    omega
  have hnot2 : g ≠ 2 := by
    intro h2
    have hfac : (a+1)*(b+1) = 4*p+1 := by omega
    have hna := hsplit (a+1) ⟨b+1,hfac.symm⟩
    have hnb := hsplit (b+1) ⟨a+1,hfac.symm.trans (Nat.mul_comm _ _)⟩
    have haa : 2 ∣ a := h2 ▸ (Nat.gcd_dvd_left a b : g ∣ a)
    have hbb : 2 ∣ b := h2 ▸ (Nat.gcd_dvd_right a b : g ∣ b)
    have ha4 : 4 ∣ a := by omega
    have hb4 : 4 ∣ b := by omega
    have hh : 4 ∣ g := Nat.dvd_gcd ha4 hb4
    omega
  by_contra! hgy
  have hgd : g ∣ 2*(2*p-1) :=
    ⟨g*(u*v)+(u+v-1),by rw [htable]; ring⟩
  obtain ⟨w,hw⟩ := hgd
  have het : 2 ∣ g*w := ⟨2*p-1,hw.symm⟩
  rcases Nat.prime_two.dvd_mul.mp het with h | h
  · obtain ⟨d,hd⟩ := h
    have hboth : 2*(2*p-1) = 2*(d*w) := by rw [hw,hd,Nat.mul_assoc]
    have hn := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hboth
    exact hrough d (by omega) (by omega) ⟨w,hn⟩
  · obtain ⟨t,ht'⟩ := h
    have hboth : 2*(2*p-1) = 2*(g*t) := by rw [hw,ht']; ring
    have hn := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hboth
    exact hrough g (by omega) hgy ⟨t,hn⟩

end A400795.Obstruction

namespace OMA.P_oeis_a400795_R1_H1

theorem main : OMA.R_oeis_a400795_R1.H1 := by
  intro p a b y
  exact A400795.Obstruction.large_gcd

end OMA.P_oeis_a400795_R1_H1

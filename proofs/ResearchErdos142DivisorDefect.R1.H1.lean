import OMAReductions.R_ResearchErdos142DivisorDefect_R1
import Mathlib

/-! Codex for dwilfand-sys. The nonzero remainder is a positive multiple
of the gcd. Equality in the product bound forces comparable divisors. -/

theorem OMA.solution : OMA.R_ResearchErdos142DivisorDefect_R1.H1 := by
  intro L g hL hg
  dsimp only
  by_cases hgL : g ∣ L
  · have he : Nat.gcd L g = g :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right L g) (Nat.dvd_gcd hgL (dvd_refl g))
    simp [Nat.mod_eq_zero_of_dvd hgL, he, hgL]
  by_cases hLg : L ∣ g
  · have hle := Nat.le_of_dvd hg hLg
    have hne : L ≠ g := by
      intro e
      subst g
      exact hgL (dvd_refl L)
    have he : Nat.gcd L g = L :=
      Nat.dvd_antisymm (Nat.gcd_dvd_left L g) (Nat.dvd_gcd (dvd_refl L) hLg)
    simp [Nat.mod_eq_of_lt (lt_of_le_of_ne hle hne), he, hLg]
  have hbpos : 0 < L % g := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hgL (Nat.dvd_of_mod_eq_zero h)
  have hdrem : Nat.gcd L g ∣ L % g := by
    have e : Nat.gcd L g = Nat.gcd (L % g) g := by
      rw [Nat.gcd_comm L g, Nat.gcd_rec g L]
    rw [e]
    exact Nat.gcd_dvd_left _ _
  have hgb := Nat.le_of_dvd hbpos hdrem
  have hbg := Nat.mod_lt L hg
  have hbL := Nat.mod_le L g
  have hgl : Nat.gcd L g ≠ L := by
    intro h
    exact hLg (h ▸ Nat.gcd_dvd_right L g)
  have hstrict : (L % g) * (g - L % g) < L * (g - Nat.gcd L g) := by
    by_cases hh : L % g < L
    · exact lt_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right hh (by omega))
        (Nat.mul_le_mul_left L (by omega))
    · have he : L % g = L := by omega
      rw [he]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hL
  exact ⟨hstrict.le, by simp [ne_of_lt hstrict, hgL, hLg]⟩

import OMAReductions.R_ResearchErdos142SupersaturationPower_R1
import Mathlib

/- Codex for @dwilfand-sys. Classical finite-set double counting, applied to
the prime cyclic progression-count plan of @eilamc14, desk note 151553. -/
namespace Erdos142SupersaturationPower

private theorem cancel {a b z : ℕ} (hz : 0 < z) (h : a*z ≤ b*z) : a ≤ b := by
  by_contra! hbad
  exact (not_lt_of_ge h) (Nat.mul_lt_mul_of_pos_right hbad hz)

private theorem scaled (m t : ℕ) (htm : t ≤ m) :
    ∀ k : ℕ, k ≤ t → m^k * t.descFactorial k ≤ t^k * m.descFactorial k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro hkt
    have h0 := ih (by omega)
    have hmk : m-k = (t-k)+(m-t) := by omega
    have hmt : t+(m-t) = m := by omega
    have pair : m*(t-k) ≤ t*(m-k) := by
      calc
        m*(t-k) = (t+(m-t))*(t-k) := by rw [hmt]
        _ = t*(t-k)+(m-t)*(t-k) := by ring
        _ ≤ t*(t-k)+(m-t)*t := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _
        _ = t*(m-k) := by rw [hmk]; ring
    rw [pow_succ, pow_succ, Nat.descFactorial_succ, Nat.descFactorial_succ]
    calc
      _ = (m^k * t.descFactorial k)*(m*(t-k)) := by ring
      _ ≤ (t^k * m.descFactorial k)*(t*(m-k)) := Nat.mul_le_mul h0 pair
      _ = _ := by ring

private theorem ratio (k t m : ℕ) (hkt : k ≤ t) (htm : t ≤ m) :
    m^k * (m-k).choose (t-k) ≤ t^k * m.choose t := by
  have h := scaled m t htm k hkt
  rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose] at h
  have hc : m^k * t.choose k ≤ t^k * m.choose k := by
    apply cancel (Nat.factorial_pos k)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  apply cancel (Nat.choose_pos hkt)
  calc
    _ = (m^k * t.choose k) * (m-k).choose (t-k) := by ring
    _ ≤ (t^k * m.choose k) * (m-k).choose (t-k) := Nat.mul_le_mul_right _ hc
    _ = t^k * (m.choose k * (m-k).choose (t-k)) := by ring
    _ = _ := by rw [← Nat.choose_mul (n := m) hkt]; ring

theorem remove_binomials : OMA.R_ResearchErdos142SupersaturationPower_R1.H1 := by
  intro k t m R E hkt htm hcount
  have hz : 0 < (m-k).choose (t-k) := Nat.choose_pos (Nat.sub_le_sub_right htm k)
  apply cancel hz
  calc
    _ = (t-R) * (m^k * (m-k).choose (t-k)) := by ring
    _ ≤ (t-R) * (t^k * m.choose t) := Nat.mul_le_mul_left _ (ratio k t m hkt htm)
    _ = t^k * ((t-R) * m.choose t) := by ring
    _ ≤ t^k * (E * (m-k).choose (t-k)) := Nat.mul_le_mul_left _ hcount
    _ = _ := by ring

end Erdos142SupersaturationPower

theorem OMA.solution : OMA.R_ResearchErdos142SupersaturationPower_R1.H1 := Erdos142SupersaturationPower.remove_binomials

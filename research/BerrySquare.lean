import OMAStatements.S_wp_rational_dense_problem

/-!
# Berry's equations for the four-distance problem

T. G. Berry, *Points at rational distance from the corners of a unit square*,
Ann. Scuola Norm. Sup. Pisa (4) 17 (1990), 505–529, p. 505, equations (1) and
(2). https://www.numdam.org/item/ASNSP_1990_4_17_4_505_0.pdf

Take the side length T = 1. Orient the square so Y is the distance to (0,0),
X and Z are the distances to (1,0) and (0,1), and U is the distance to (1,1).
The inverse formulas work on the whole real plane. Signed rational roots in
the polynomial system give distances by taking absolute values.
-/

namespace OMA.BerrySquare

open OMA.S_wp_rational_dense_problem

def FourCorners (x y : ℝ) : Prop :=
  HasRationalDistance x y 0 0 ∧ HasRationalDistance x y 1 0 ∧
  HasRationalDistance x y 0 1 ∧ HasRationalDistance x y 1 1

def BerryEquations (X Y Z U : ℚ) : Prop :=
  2 * (Y ^ 4 + 1) + X ^ 4 + Z ^ 4 =
    2 * (X ^ 2 + Z ^ 2) * (Y ^ 2 + 1) ∧
  U ^ 2 + Y ^ 2 = X ^ 2 + Z ^ 2

theorem distance_iff_square (x y a b : ℝ) :
    HasRationalDistance x y a b ↔
      ∃ r : ℚ, (r : ℝ) ^ 2 = (x - a) ^ 2 + (y - b) ^ 2 := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [← hr, Real.sq_sqrt (by positivity)]⟩
  · rintro ⟨r, hr⟩
    exact ⟨|r|, by rw [← hr, Real.sqrt_sq_eq_abs, Rat.cast_abs]⟩

private theorem geometry {x y X Y Z U : ℝ}
    (hY : Y ^ 2 = x ^ 2 + y ^ 2) (hX : X ^ 2 = (x - 1) ^ 2 + y ^ 2)
    (hZ : Z ^ 2 = x ^ 2 + (y - 1) ^ 2)
    (hU : U ^ 2 = (x - 1) ^ 2 + (y - 1) ^ 2) :
    2 * (Y ^ 4 + 1) + X ^ 4 + Z ^ 4 = 2 * (X ^ 2 + Z ^ 2) * (Y ^ 2 + 1) ∧
      U ^ 2 + Y ^ 2 = X ^ 2 + Z ^ 2 := by
  constructor
  · have fourth (v : ℝ) : v ^ 4 = (v ^ 2) ^ 2 := by ring
    rw [fourth Y, fourth X, fourth Z, hX, hY, hZ]
    ring
  · rw [hU, hY, hX, hZ]
    ring

theorem equations_of_point {x y : ℝ} (h : FourCorners x y) :
    ∃ X Y Z U : ℚ, BerryEquations X Y Z U ∧
      x = (((1 + Y ^ 2 - X ^ 2) / 2 : ℚ) : ℝ) ∧
      y = (((1 + Y ^ 2 - Z ^ 2) / 2 : ℚ) : ℝ) ∧
      (Y : ℝ) ^ 2 = x ^ 2 + y ^ 2 := by
  obtain ⟨h₀₀, h₁₀, h₀₁, h₁₁⟩ := h
  obtain ⟨Y, hY⟩ := (distance_iff_square ..).mp h₀₀
  obtain ⟨X, hX⟩ := (distance_iff_square ..).mp h₁₀
  obtain ⟨Z, hZ⟩ := (distance_iff_square ..).mp h₀₁
  obtain ⟨U, hU⟩ := (distance_iff_square ..).mp h₁₁
  simp only [sub_zero] at hY hX hZ
  obtain ⟨hquartic, hquadratic⟩ := geometry hY hX hZ hU
  refine ⟨X, Y, Z, U, ⟨?_, ?_⟩, ?_, ?_, hY⟩
  · exact_mod_cast hquartic
  · exact_mod_cast hquadratic
  · push_cast
    linear_combination (1 / 2 : ℝ) * hX - (1 / 2 : ℝ) * hY
  · push_cast
    linear_combination (1 / 2 : ℝ) * hZ - (1 / 2 : ℝ) * hY

/-- Rational coordinates recovered from three signed rational lengths satisfy
the three required distance identities as soon as Berry's quartic vanishes. -/
theorem reconstruct_three {X Y Z : ℚ}
    (hquartic : 2 * (Y ^ 4 + 1) + X ^ 4 + Z ^ 4 =
      2 * (X ^ 2 + Z ^ 2) * (Y ^ 2 + 1)) :
    let x := (1 + Y ^ 2 - X ^ 2) / 2
    let y := (1 + Y ^ 2 - Z ^ 2) / 2
    Y ^ 2 = x ^ 2 + y ^ 2 ∧ X ^ 2 = (x - 1) ^ 2 + y ^ 2 ∧
      Z ^ 2 = x ^ 2 + (y - 1) ^ 2 := by
  let x : ℚ := (1 + Y ^ 2 - X ^ 2) / 2
  let y : ℚ := (1 + Y ^ 2 - Z ^ 2) / 2
  have hx : 2 * x = 1 + Y ^ 2 - X ^ 2 := by dsimp [x]; ring
  have hy : 2 * y = 1 + Y ^ 2 - Z ^ 2 := by dsimp [y]; ring
  have hY : Y ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [x, y]
    linear_combination -(1 / 4 : ℚ) * hquartic
  refine ⟨hY, ?_, ?_⟩
  · change X ^ 2 = (x - 1) ^ 2 + y ^ 2
    nlinarith only [hY, hx]
  · change Z ^ 2 = x ^ 2 + (y - 1) ^ 2
    nlinarith only [hY, hy]

theorem point_of_equations {X Y Z U : ℚ} (h : BerryEquations X Y Z U) :
    FourCorners (((1 + Y ^ 2 - X ^ 2) / 2 : ℚ) : ℝ)
      (((1 + Y ^ 2 - Z ^ 2) / 2 : ℚ) : ℝ) := by
  obtain ⟨hquartic, hquadratic⟩ := h
  let x : ℚ := (1 + Y ^ 2 - X ^ 2) / 2
  let y : ℚ := (1 + Y ^ 2 - Z ^ 2) / 2
  have hs : Y ^ 2 = x ^ 2 + y ^ 2 ∧ X ^ 2 = (x - 1) ^ 2 + y ^ 2 ∧
      Z ^ 2 = x ^ 2 + (y - 1) ^ 2 := reconstruct_three hquartic
  obtain ⟨hY, hX, hZ⟩ := hs
  have hU : U ^ 2 = (x - 1) ^ 2 + (y - 1) ^ 2 := by
    nlinarith only [hquadratic, hX, hZ, hY]
  change FourCorners (x : ℝ) (y : ℝ)
  unfold FourCorners
  simp only [distance_iff_square, sub_zero]
  refine ⟨⟨Y, ?_⟩, ⟨X, ?_⟩, ⟨Z, ?_⟩, ⟨U, ?_⟩⟩
  · exact_mod_cast hY
  · exact_mod_cast hX
  · exact_mod_cast hZ
  · exact_mod_cast hU

/-- The exact statement of the four-distance problem is equivalent to Berry's
two polynomial equations over the rationals. -/
theorem statement_iff_berry :
    (∃ x y : ℝ, HasRationalDistance x y 0 0 ∧ HasRationalDistance x y 1 0 ∧
      HasRationalDistance x y 0 1 ∧ HasRationalDistance x y 1 1) ↔
    ∃ X Y Z U : ℚ, BerryEquations X Y Z U := by
  constructor
  · rintro ⟨x, y, hp⟩
    obtain ⟨X, Y, Z, U, he, _⟩ := equations_of_point (x := x) (y := y) hp
    exact ⟨X, Y, Z, U, he⟩
  · rintro ⟨X, Y, Z, U, he⟩
    exact ⟨_, _, point_of_equations he⟩

end OMA.BerrySquare

namespace OMA.BerrySquare

private theorem eq_zero_of_twice_square {r s : ℚ} (h : r ^ 2 = 2 * s ^ 2) :
    s = 0 := by
  by_contra hs
  have hsq : IsSquare (2 : ℚ) := by
    refine ⟨r / s, ?_⟩
    field_simp [hs] <;> nlinarith only [h]
  exact (by norm_num : ¬IsSquare (2 : ℚ)) hsq

/-- The rational four-distance equations have no point on the section
corresponding to the circumcircle of the original square. -/
theorem excluded_circle_section {X Y Z U : ℚ} (he : BerryEquations X Y Z U) :
    X ^ 2 + Z ^ 2 ≠ 2 := by
  intro hc
  obtain ⟨hqu, hbi⟩ := he
  have hprod : (X * Z - (Y ^ 2 - 1)) * (X * Z + (Y ^ 2 - 1)) = 0 := by
    linear_combination -(1 / 2 : ℚ) * hqu +
      ((X ^ 2 + Z ^ 2 - 2 * Y ^ 2) / 2) * hc
  have reject (r s : ℚ) (hr : r ^ 2 = 2 * Y ^ 2) (hs : s ^ 2 = 2 * U ^ 2) :
      False := by
    have hY := eq_zero_of_twice_square hr
    have hU := eq_zero_of_twice_square hs
    rw [hY, hU] at hbi
    linarith only [hbi, hc]
  rcases mul_eq_zero.mp hprod with hp | hp
  · apply reject (X + Z) (X - Z) <;> nlinarith only [hc, hbi, hp]
  · apply reject (X - Z) (X + Z) <;> nlinarith only [hc, hbi, hp]

/-- This includes the four corners. The circle equation is equivalent to
`(x - 1/2)^2 + (y - 1/2)^2 = 1/2`. -/
theorem no_four_distances_on_circumcircle {x y : ℝ} (hc : x ^ 2 + y ^ 2 = x + y) :
    ¬FourCorners x y := by
  intro h
  obtain ⟨X, Y, Z, U, he, hx, hy, hY⟩ := equations_of_point h
  push_cast at hx hy
  have hsum : (X : ℝ) ^ 2 + (Z : ℝ) ^ 2 = 2 := by
    linarith only [hx, hy, hY, hc]
  exact excluded_circle_section he (by exact_mod_cast hsum)

end OMA.BerrySquare

/-!
# Berry's degree-four family of rational three-distance points

T. G. Berry, *Points at rational distance from the corners of a unit square*
(1990), Table 4 on p. 528 and Proposition 4.4 on p. 526.
The table gives homogeneous signed distances and the side length. The final
theorem normalizes by that side length and rules out a rational fourth distance.
-/

namespace SquareDistance.Berry

def tableX (t : ℚ) := 5*t^4 - 48*t^3 + 144*t^2 - 128*t + 64
def tableY (t : ℚ) := 4*t^4 - 48*t^3 + 192*t^2 - 384*t + 256
def tableZ (t : ℚ) := t^4 - 16*t^3 + 144*t^2 - 384*t + 320
def tableT (t : ℚ) := (tableX t + tableZ t) / 2

theorem table_quartic (t : ℚ) :
    2 * (tableY t ^ 4 + tableT t ^ 4) + tableX t ^ 4 + tableZ t ^ 4 =
      2 * (tableX t ^ 2 + tableZ t ^ 2) * (tableY t ^ 2 + tableT t ^ 2) := by
  unfold tableT tableX tableY tableZ
  ring

theorem tableT_pos (t : ℚ) : 0 < tableT t := by
  calc
    0 < ((t-4)^2 + 8) * (3*(t-4/3)^2 + 8/3) := by positivity
    _ = tableT t := by unfold tableT tableX tableZ; ring

private def quartic (a b : ℚ) : ℚ :=
  2 * (5*a^4 - 64*a^3*b + 304*a^2*b^2 - 512*a*b^3 + 320*b^4)

private theorem table_factor (t : ℚ) :
    tableX t ^ 2 + tableZ t ^ 2 - tableY t ^ 2 = (t^2-8)^2 * quartic t 1 := by
  unfold tableX tableY tableZ quartic
  ring

-- An odd a makes 2(5a⁴+4e) equal to 2 modulo 4. A rational square
-- which is an integer must already be the square of an integer.
private lemma scaled_obstruction (a e : ℤ) (s z : ℚ) (ha : Odd a) (hs : s ≠ 0) :
    z ^ 2 ≠ s ^ 2 * (2 * (5*(a:ℚ)^4 + 4*(e:ℚ))) := by
  intro hz
  have hq : IsSquare ((2 * (5*a^4 + 4*e) : ℤ) : ℚ) := by
    refine ⟨z / s, ?_⟩
    rw [← pow_two, div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hs)).mpr
    push_cast
    nlinarith only [hz]
  obtain ⟨v, hv⟩ := Rat.isSquare_intCast_iff.mp hq
  obtain ⟨k, rfl⟩ := ha
  have hm := congrArg (Int.castRingHom (ZMod 4)) hv
  have h4 : ∀ k e v : ZMod 4, 2*(5*(2*k+1)^4 + 4*e) ≠ v*v := by decide
  exact h4 (k:ZMod 4) (e:ZMod 4) (v:ZMod 4) (by simpa using hm)

-- For a primitive fraction a/b, the three cases v₂(a) = 0, = 1, and ≥ 2
-- give a square scaling factor of 1, 4², or 8², followed by 2 times an odd integer.
private theorem primitive_obstruction (a b : ℤ) (hc : IsCoprime a b) (z : ℚ) :
    z ^ 2 ≠ quartic (a:ℚ) (b:ℚ) := by
  intro hz
  rcases a.even_or_odd with he | ho
  · have hb : Odd b := Int.isCoprime_two_left.mp (hc.of_isCoprime_of_dvd_left he.two_dvd)
    obtain ⟨c, h⟩ := he.two_dvd
    rw [h] at hz
    rcases c.even_or_odd with he' | ho'
    · obtain ⟨d, hd⟩ := he'.two_dvd
      rw [hd] at hz
      apply scaled_obstruction b (-8*b^3*d + 19*b^2*d^2 - 16*b*d^3 + 5*d^4)
        8 z hb (by norm_num)
      calc
        _ = _ := hz
        _ = _ := by unfold quartic; push_cast; ring
    · apply scaled_obstruction c (-8*c^3*b + 19*c^2*b^2 - 16*c*b^3 + 5*b^4)
        4 z ho' (by norm_num)
      calc
        _ = _ := hz
        _ = _ := by unfold quartic; push_cast; ring
  · apply scaled_obstruction a (-16*a^3*b + 76*a^2*b^2 - 128*a*b^3 + 80*b^4)
      1 z ho (by norm_num)
    calc
      _ = _ := hz
      _ = _ := by unfold quartic; push_cast; ring

private theorem quartic_obstruction (t z : ℚ) : z ^ 2 ≠ quartic t 1 := by
  intro hz
  have hd : (t.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr t.den_nz
  have hn : (t.num : ℚ) = t * (t.den : ℚ) := (div_eq_iff hd).mp t.num_div_den
  apply primitive_obstruction t.num (t.den:ℤ) t.isCoprime_num_den (z*(t.den:ℚ)^2)
  simp only [Int.cast_natCast]
  rw [hn]
  calc
    _ = z^2 * (t.den:ℚ)^4 := by ring
    _ = _ := by rw [hz]; unfold quartic; ring

theorem table_no_fourth_distance (t u : ℚ) :
    u^2 + tableY t ^ 2 ≠ tableX t ^ 2 + tableZ t ^ 2 := by
  intro h
  have ht : t^2-8 ≠ 0 := by
    intro he
    have hs : IsSquare (8:ℚ) := ⟨t, by nlinarith only [he]⟩
    exact (by norm_num : ¬ IsSquare (8:ℚ)) hs
  apply quartic_obstruction t (u / (t^2-8))
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 ht)).mpr
  nlinarith only [h, table_factor t]

theorem unit_table_no_fourth_distance (t u : ℚ) :
    u^2 + (tableY t / tableT t)^2 ≠
      (tableX t / tableT t)^2 + (tableZ t / tableT t)^2 := by
  intro hu
  apply table_no_fourth_distance t (u * tableT t)
  have ht := (tableT_pos t).ne'
  calc
    _ = tableT t ^ 2 * (u^2 + (tableY t / tableT t)^2) := by field_simp [ht] <;> ring
    _ = tableT t ^ 2 * ((tableX t / tableT t)^2 + (tableZ t / tableT t)^2) := by rw [hu]
    _ = _ := by field_simp [ht] <;> ring

/-- The leading coefficients also exclude the projective parameter at infinity. -/
theorem unit_table_infinity_no_fourth_distance (u : ℚ) :
    u^2 + (4/3:ℚ)^2 ≠ (5/3:ℚ)^2 + (1/3:ℚ)^2 := by
  intro hu
  have hs : IsSquare (10:ℚ) := ⟨3*u, by nlinarith only [hu]⟩
  exact (by norm_num : ¬ IsSquare (10:ℚ)) hs

end SquareDistance.Berry

namespace OMA.BerrySquare

open SquareDistance.Berry OMA.S_wp_rational_dense_problem

/-- The reconstructed point in Berry's degree-four family has rational distances
to the first three vertices and an irrational distance to the fourth, for
every rational parameter. -/
theorem family_three_and_only_three (t : ℚ) :
    let X := tableX t / tableT t
    let Y := tableY t / tableT t
    let Z := tableZ t / tableT t
    let x : ℚ := (1 + Y ^ 2 - X ^ 2) / 2
    let y : ℚ := (1 + Y ^ 2 - Z ^ 2) / 2
    HasRationalDistance x y 0 0 ∧ HasRationalDistance x y 1 0 ∧
    HasRationalDistance x y 0 1 ∧ ¬HasRationalDistance x y 1 1 := by
  let X := tableX t / tableT t
  let Y := tableY t / tableT t
  let Z := tableZ t / tableT t
  let x := (1 + Y ^ 2 - X ^ 2) / 2
  let y := (1 + Y ^ 2 - Z ^ 2) / 2
  have hquart : 2 * (Y ^ 4 + 1) + X ^ 4 + Z ^ 4 =
      2 * (X ^ 2 + Z ^ 2) * (Y ^ 2 + 1) := by
    have hscaled := congrArg (fun d : ℚ => d / tableT t ^ 4) (table_quartic t)
    convert hscaled using 1 <;> dsimp only [X, Y, Z] <;>
      field_simp [(tableT_pos t).ne'] <;> ring
  have hs : Y ^ 2 = x ^ 2 + y ^ 2 ∧ X ^ 2 = (x - 1) ^ 2 + y ^ 2 ∧
      Z ^ 2 = x ^ 2 + (y - 1) ^ 2 := reconstruct_three hquart
  obtain ⟨hY, hX, hZ⟩ := hs
  change HasRationalDistance x y 0 0 ∧ HasRationalDistance x y 1 0 ∧
    HasRationalDistance x y 0 1 ∧ ¬HasRationalDistance x y 1 1
  simp only [distance_iff_square, sub_zero]
  refine ⟨⟨Y, ?_⟩, ⟨X, ?_⟩, ⟨Z, ?_⟩, ?_⟩
  · exact_mod_cast hY
  · exact_mod_cast hX
  · exact_mod_cast hZ
  · rintro ⟨u, hu⟩
    have hu' : u ^ 2 = (x - 1) ^ 2 + (y - 1) ^ 2 := by exact_mod_cast hu
    apply unit_table_no_fourth_distance t u
    change u ^ 2 + Y ^ 2 = X ^ 2 + Z ^ 2
    nlinarith only [hY, hX, hZ, hu']

end OMA.BerrySquare

#print axioms OMA.BerrySquare.statement_iff_berry

#print axioms OMA.BerrySquare.no_four_distances_on_circumcircle

#print axioms OMA.BerrySquare.family_three_and_only_three

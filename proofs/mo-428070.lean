import OMAStatements.S_mo_428070
import Mathlib

/-!
# mo-428070: no finite group algebra over ℚ contains a square root of 2

The augmentation `ℚ[G] → ℚ`, which sends every group element to `1`, is a ring homomorphism.
If `x ^ 2 = 2` in `ℚ[G]`, its image `q` is a rational number with `q ^ 2 = 2`, which contradicts
the irrationality of the square root of 2. Finiteness of `G` is not used.

Proof found by Claude Code (claude-fable-5-2) for @dwilfand-sys.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_428070.main) := by
  rintro ⟨G, hG, -, x, hx⟩
  -- the augmentation map, kept opaque so that rewriting cannot unfold it
  obtain ⟨aug, -⟩ : ∃ aug : MonoidAlgebra ℚ G →ₐ[ℚ] ℚ, True :=
    ⟨MonoidAlgebra.lift _ _ _ (1 : G →* ℚ), trivial⟩
  have h1 : aug x ^ 2 = 2 := by
    have h := congrArg aug hx
    simpa only [map_pow, map_ofNat] using h
  have hq : Real.sqrt 2 = |((aug x : ℚ) : ℝ)| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    exact_mod_cast h1.symm
  exact irrational_sqrt_two.ne_rat |aug x| (by rw [hq, Rat.cast_abs])

import OMAStatements.S_mo_258600
import Mathlib

/-!
# mo-258600: a surjective ring homomorphism need not induce a surjection on GL_n

Counterexample for `n = 2`: the reduction map `ℤ → ZMod 5`.
The determinant of an invertible integer matrix is a unit of `ℤ`, so it is `1` or `-1`, and the
determinant commutes with ring homomorphisms. The matrix `diag(2, 1)` is invertible over `ZMod 5`
(its inverse is `diag(3, 1)`) and has determinant `2`, which is neither `1` nor `-1` in `ZMod 5`.
So it is not the image of any element of `GL_2(ℤ)`. The same argument works for every `n ≥ 1`.

Proof found by Claude Code (claude-fable-5-2) for @dwilfand-sys.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_258600.main) := by
  intro h
  have hsurj : Function.Surjective (Int.castRingHom (ZMod 5)) :=
    ZMod.ringHom_surjective (Int.castRingHom (ZMod 5))
  let u : (Matrix (Fin 2) (Fin 2) (ZMod 5))ˣ :=
    ⟨!![2, 0; 0, 1], !![3, 0; 0, 1],
      by first | decide | (simp [Matrix.mul_fin_two, Matrix.one_fin_two] <;> decide),
      by first | decide | (simp [Matrix.mul_fin_two, Matrix.one_fin_two] <;> decide)⟩
  obtain ⟨M, hM⟩ := h ℤ (ZMod 5) (Int.castRingHom (ZMod 5)) hsurj 2 (by norm_num) u
  have hval : RingHom.mapMatrix (Int.castRingHom (ZMod 5)) (M : Matrix (Fin 2) (Fin 2) ℤ)
      = !![2, 0; 0, 1] := by
    first
      | exact congrArg Units.val hM
      | simpa [OMA.S_mo_258600.glMap] using congrArg Units.val hM
  have hdet : (Int.castRingHom (ZMod 5)) (M : Matrix (Fin 2) (Fin 2) ℤ).det = 2 := by
    rw [RingHom.map_det, hval]
    first
      | simp [Matrix.det_fin_two_of]
      | decide
  have hunit : IsUnit (M : Matrix (Fin 2) (Fin 2) ℤ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · have h2 : (2 : ZMod 5) = 1 := by
      rw [← hdet, h1, map_one]
    exact absurd h2 (by decide)
  · have h2 : (2 : ZMod 5) = -1 := by
      rw [← hdet, h1, map_neg, map_one]
    exact absurd h2 (by decide)

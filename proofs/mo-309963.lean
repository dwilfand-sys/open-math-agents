import OMAStatements.S_mo_309963
import Mathlib

/-!
# mo-309963: the determinant over the small field is the norm of the determinant

This is a classical fact, and Mathlib has it as `LinearMap.det_restrictScalars`, for free modules
over commutative rings. Separability of `E/F` is not needed.

Found by Claude Code (claude-fable-5-2) for @dwilfand-sys.
-/

theorem OMA.solution : type_of% @OMA.S_mo_309963.main := by
  intro F E V _ _ _ _ _ _ _ _ _ _ T
  exact LinearMap.det_restrictScalars

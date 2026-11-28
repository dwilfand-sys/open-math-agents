import OMAReductions.R_ResearchErdos357RSBalanced32_R1
import Mathlib.Tactic.Ring

/-! Codex for dwilfand-sys. The eight witness pairs work for all four tile
letters, and lie entirely in the first 32 positions. -/

namespace RSBalanced32
open OMA.R_ResearchErdos357RSBalanced32_R1

private def start (C : Fin 8) : ℕ :=
  (#[14, 23, 14, 21, 14, 11, 14, 9] : Array ℕ)[C.val]!
private def spanSize (C : Fin 8) : ℕ := if C.val % 2 = 0 then 2 else 8

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
private theorem table : ∀ C : Fin 8,
    (spanSize C = 2 ∨ spanSize C = 8) ∧ 1 ≤ start C ∧ start C + spanSize C < 32 ∧
    (C.val + start C) % spanSize C = 0 ∧ ∀ v : Fin 4,
      tileAt 6 v (start C-1) = tileAt 6 v (start C+spanSize C-1) ∧
      tileAt 6 v (start C) = tileAt 6 v (start C+spanSize C) ∧
      lightCount v (start C) (spanSize C) = spanSize C/2 := by decide

theorem certificate : H1 := by
  constructor
  · intro C
    exact ⟨start C, spanSize C, table C⟩
  · intro xs delta
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih, add_mul] <;> ring

end RSBalanced32

theorem OMA.solution : OMA.R_ResearchErdos357RSBalanced32_R1.H1 := RSBalanced32.certificate

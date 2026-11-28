import OMAReductions.R_ResearchErdos142OrbitAveraging_R1
import Mathlib

/-! Codex for dwilfand-sys. Reindex columns by the transitivity permutations,
then rows by the individual orbit permutations, and use finite Fubini. -/
namespace OrbitAveraging
open OMA.R_ResearchErdos142OrbitAveraging_R1

theorem average : H1 := by
  intro R D row transport w x
  have same (y : Fin D) : (∑ g, w (row g x))=∑ g,w (row g y) := by
    obtain ⟨tr,ht⟩ := transport x y
    calc
      _ = ∑ g,w (row (tr g) x) := (Equiv.sum_comp tr (fun g => w (row g x))).symm
      _ = _ := Finset.sum_congr rfl (fun g _ => congrArg w (ht g))
  calc
    _ = ∑ _y : Fin D, ∑ g,w (row g x) := by simp
    _ = ∑ y,∑ g,w (row g y) := Finset.sum_congr rfl (fun y _ => same y)
    _ = ∑ g,∑ y,w (row g y) := Finset.sum_comm
    _ = ∑ _g : Fin R, ∑ y,w y := Finset.sum_congr rfl (fun g _ => Equiv.sum_comp (row g) w)
    _ = _ := by simp

end OrbitAveraging

theorem OMA.solution : OMA.R_ResearchErdos142OrbitAveraging_R1.H1 := OrbitAveraging.average

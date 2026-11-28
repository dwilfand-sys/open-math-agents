import OMAReductions.R_ResearchErdos142Mask49_R1
import Mathlib.Tactic.Abel

/- Codex for dwilfand-sys. The affine masks specialize the prime-digit construction
   inspired by Deldor14's full-cycle dilation. The lower certificate consists of
   15 explicit progressions. All table entries are verified inside Lean. -/

namespace Mask49
open OMA.R_ResearchErdos142Mask49_R1

private def lineStart (t : Fin 15) : Fin 49 :=
  (#[1, 22, 34, 33, 9, 1, 28, 6, 23, 10, 3, 46, 29, 16, 3] : Array (Fin 49))[t.val]!

private def lineStep (t : Fin 15) : Fin 49 :=
  (#[1, 1, 12, 3, 13, 9, 4, 20, 17, 5, 3, 23, 8, 23, 4] : Array (Fin 49))[t.val]!

private def safe (t : Fin 15) (x : Fin 49) : Bool :=
  let mask := (#[562949684985857, 4194303, 423277881261063, 80422649041481, 119380303881417, 337659805721393, 112571683386163, 164147901016725, 187283461024341, 449451978941241, 241259357217939, 160844069769819, 494512902365665, 401478826740005, 337769972052241] : Array ℕ)[t.val]!
  mask.testBit x.val

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem hits : ∀ a d : Fin 49, d.val % 7 ≠ 0 → ∃ j : Fin 28,
    point a d j.val = 0 ∨ point a d j.val = 7 ∨ point a d j.val = 21 := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem cover : ∀ b c : Fin 49, ∃ t : Fin 15,
    safe t b = true ∧ safe t c = true := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem sound : ∀ t : Fin 15, (lineStep t).val % 7 ≠ 0 ∧
    ∀ j : Fin 27, let x := point (lineStart t) (lineStep t) j.val
                  x ≠ 0 ∧ safe t x = false := by
  decide

private theorem normalized (b c : Fin 49) :
    ∃ a d : Fin 49, d.val % 7 ≠ 0 ∧ ∀ j : Fin 27,
      point a d j.val ≠ 0 ∧ point a d j.val ≠ b ∧ point a d j.val ≠ c := by
  obtain ⟨t, hb, hc⟩ := cover b c
  obtain ⟨hd, h⟩ := sound t
  refine ⟨lineStart t, lineStep t, hd, ?_⟩
  intro j
  obtain ⟨hz, hn⟩ := h j
  refine ⟨hz, ?_, ?_⟩
  · intro he
    rw [he, hb] at hn
    contradiction
  · intro he
    rw [he, hc] at hn
    contradiction

theorem optimal : H1 := by
  refine ⟨hits, ?_⟩
  intro x y z
  obtain ⟨a, d, hd, h⟩ := normalized (y - x) (z - x)
  refine ⟨x + a, d, hd, ?_⟩
  intro j
  have hshift (w : Fin 49) (he : x + point a d j.val = w) :
      point a d j.val = w - x := by rw [← he]; abel
  rw [show point (x + a) d j.val = x + point a d j.val by
    simp only [point, add_assoc]]
  obtain ⟨h0, hy, hz⟩ := h j
  exact ⟨fun he => h0 (by simpa using hshift x he),
         fun he => hy (hshift y he), fun he => hz (hshift z he)⟩

end Mask49

theorem OMA.solution : OMA.R_ResearchErdos142Mask49_R1.H1 := Mask49.optimal

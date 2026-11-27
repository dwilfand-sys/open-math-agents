import Mathlib

/-! Carter's sparse scales case, word `0x3da1087`. For each of the four
enumerated inside configurations, two specified two-secants cannot meet at a
hidden point. The input tables give the two-secants through each support
point and each of the 44 nonhidden exterior points. Their enumeration is a
separate mathematical assertion. The historical search and SAT results are
due to Carter, Lam, Thiel, Swiercz, Bright and coauthors.
-/

namespace CarterScalesTerminal

def supportPencils : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8],
  [9, 10, 11, 12, 13, 14, 15, 16, 17],
  [18, 19, 20, 21, 22, 23, 24, 25, 26],
  [27, 28, 29, 30, 31, 32, 33, 34, 35],
  [0, 9, 18, 27, 36, 37, 38, 39, 40],
  [10, 19, 28, 41, 42, 43, 44, 45, 46],
  [1, 20, 29, 47, 48, 49, 50, 51, 52],
  [2, 11, 30, 53, 54, 55, 56, 57, 58],
  [3, 12, 21, 31, 41, 47, 53, 59, 60],
  [13, 22, 32, 36, 48, 54, 61, 62, 63],
  [4, 23, 33, 37, 42, 55, 64, 65, 66],
  [5, 14, 34, 38, 43, 49, 67, 68, 69],
  [15, 24, 35, 50, 56, 64, 67, 70, 71],
  [6, 16, 25, 44, 51, 57, 61, 65, 68],
  [7, 26, 39, 45, 58, 59, 62, 69, 70],
  [8, 17, 40, 46, 52, 60, 63, 66, 71]
]

/-- Two distinct lines through a new point have no previously assigned meeting. -/
def canShare (inside : List (List ℕ)) (x y : ℕ) : Bool :=
  x == y || !(supportPencils ++ inside).any (fun lines => lines.contains x && lines.contains y)

/-- Choose a line from each required pencil, subject to pairwise compatibility. -/
def complete? (ok : ℕ → ℕ → Bool) : List (List ℕ) → List ℕ → Bool
  | [], _ => true
  | row :: rest, seen =>
    if row.any (fun x => seen.contains x) then complete? ok rest seen
    else row.any (fun x => seen.all (ok x) && complete? ok rest (x :: seen))

theorem complete_of_witness (ok : ℕ → ℕ → Bool) (Through : ℕ → Prop)
    (pair : ∀ x y, Through x → Through y → ok x y = true) (rows : List (List ℕ)) :
    ∀ seen : List ℕ, (∀ row ∈ rows, ∃ x ∈ row, Through x) →
      (∀ x ∈ seen, Through x) → complete? ok rows seen = true := by
  induction rows with
  | nil => intro _ _ _; rfl
  | cons row rest ih =>
    intro seen cover chosen
    have tail : ∀ line ∈ rest, ∃ x ∈ line, Through x :=
      fun line member => cover line (List.mem_cons_of_mem _ member)
    simp only [complete?]
    split
    · exact ih seen tail chosen
    · obtain ⟨x, hx, hp⟩ := cover row (by simp)
      apply List.any_eq_true.mpr
      refine ⟨x, hx, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
      · exact List.all_eq_true.mpr (fun y hy => pair x y hp (chosen y hy))
      · apply ih (x :: seen) tail
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hp
        · exact chosen y hy

theorem impossible_of_check (inside : List (List ℕ)) (b : ℕ)
    (checked : complete? (canShare inside) supportPencils [b, 35] = false)
    (Through : ℕ → Prop)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, Through x)
    (pair : ∀ x y, Through x → Through y → canShare inside x y = true) :
    ¬ (Through b ∧ Through 35) := by
  rintro ⟨hb, anchor⟩
  have yes := complete_of_witness _ Through pair supportPencils [b, 35] cover (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hb
    · exact anchor)
  rw [checked] at yes
  contradiction

def inside0 : List (List ℕ) := [
  [38, 42, 50, 58, 60, 61],
  [39, 41, 52, 54, 65, 67],
  [36, 44, 49, 53, 66, 70],
  [37, 43, 47, 57, 62, 71],
  [59, 63, 64, 68],
  [40, 45, 51, 56],
  [46, 48, 55, 69],
  [5, 15, 25, 31, 62, 66],
  [8, 12, 24, 32, 65, 69],
  [4, 16, 22, 34, 60, 70],
  [7, 14, 21, 33, 61, 71],
  [6, 17, 26, 35],
  [3, 13, 23, 67],
  [7, 15, 18, 30, 44, 52],
  [0, 16, 24, 29, 46, 58],
  [8, 10, 20, 27, 57, 70],
  [1, 11, 25, 28, 39, 71],
  [2, 9, 19, 50],
  [5, 10, 22, 33, 52, 58],
  [2, 17, 23, 28, 49, 62],
  [1, 14, 26, 30, 42, 63],
  [7, 11, 20, 32, 43, 66],
  [8, 19, 34, 54],
  [4, 13, 29, 45],
  [17, 25, 29, 38, 55, 59],
  [11, 26, 27, 49, 60, 65],
  [12, 18, 34, 51, 58, 66],
  [9, 23, 31, 52, 57, 69],
  [21, 30, 40, 68],
  [16, 33, 39, 47],
  [14, 20, 37, 53],
  [5, 24, 28, 36, 57, 60],
  [3, 25, 27, 43, 56, 63],
  [6, 18, 32, 46, 53, 67],
  [2, 22, 31, 38, 44, 71],
  [0, 35, 41, 61],
  [6, 15, 28, 37, 48, 59],
  [1, 12, 27, 44, 62, 64],
  [7, 10, 31, 36, 50, 65],
  [3, 9, 32, 42, 51, 70],
  [4, 10, 24, 38, 47, 54],
  [1, 15, 21, 36, 43, 55],
  [0, 12, 22, 42, 49, 56],
  [5, 11, 18, 41, 48, 64]
]

set_option maxRecDepth 16000 in
private theorem check0 : complete? (canShare inside0) supportPencils [1, 35] = false := by
  decide +kernel

theorem no_hidden_meeting_0 (Through : ℕ → Prop)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, Through x)
    (pair : ∀ x y, Through x → Through y → canShare inside0 x y = true) :
    ¬ (Through 1 ∧ Through 35) := impossible_of_check _ _ check0 Through cover pair

def inside1 : List (List ℕ) := [
  [39, 46, 49, 53, 61, 64],
  [38, 41, 51, 56, 62, 66],
  [37, 43, 48, 57, 60, 70],
  [36, 45, 47, 55, 68, 71],
  [59, 63, 65, 67],
  [40, 44, 50, 58],
  [42, 52, 54, 69],
  [7, 15, 22, 31, 66, 68],
  [4, 16, 24, 32, 60, 69],
  [8, 12, 23, 34, 61, 70],
  [3, 14, 25, 33, 62, 71],
  [6, 17, 26, 35],
  [5, 13, 21, 64],
  [0, 15, 25, 30, 45, 52],
  [8, 10, 24, 29, 39, 57],
  [2, 16, 20, 27, 46, 70],
  [7, 11, 18, 28, 51, 71],
  [1, 9, 19, 56],
  [7, 17, 19, 34, 48, 55],
  [5, 11, 23, 29, 46, 62],
  [4, 14, 20, 28, 58, 63],
  [2, 10, 26, 32, 49, 66],
  [8, 22, 30, 43],
  [1, 13, 33, 45],
  [14, 23, 30, 39, 51, 60],
  [17, 18, 31, 49, 58, 65],
  [9, 26, 33, 52, 53, 68],
  [11, 25, 27, 47, 66, 69],
  [21, 34, 40, 57],
  [16, 29, 37, 59],
  [12, 20, 38, 55],
  [5, 24, 27, 44, 53, 63],
  [2, 25, 28, 36, 60, 67],
  [3, 18, 32, 46, 56, 68],
  [6, 19, 31, 38, 54, 71],
  [0, 35, 41, 61],
  [6, 12, 27, 42, 50, 62],
  [7, 9, 32, 44, 47, 64],
  [3, 15, 28, 39, 48, 65],
  [4, 10, 31, 36, 51, 70],
  [3, 11, 24, 36, 42, 49],
  [2, 14, 22, 37, 41, 50],
  [4, 15, 18, 43, 47, 54],
  [0, 10, 23, 48, 53, 67]
]

set_option maxRecDepth 16000 in
private theorem check1 : complete? (canShare inside1) supportPencils [3, 35] = false := by
  decide +kernel

theorem no_hidden_meeting_1 (Through : ℕ → Prop)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, Through x)
    (pair : ∀ x y, Through x → Through y → canShare inside1 x y = true) :
    ¬ (Through 3 ∧ Through 35) := impossible_of_check _ _ check1 Through cover pair

def inside2 : List (List ℕ) := [
  [40, 45, 47, 55, 61, 67],
  [37, 41, 50, 57, 63, 69],
  [36, 46, 49, 53, 65, 70],
  [38, 42, 51, 54, 59, 71],
  [60, 62, 64, 68],
  [39, 44, 52, 56],
  [43, 48, 58, 66],
  [5, 15, 25, 32, 59, 66],
  [8, 13, 24, 31, 65, 69],
  [3, 16, 23, 34, 63, 70],
  [7, 14, 21, 33, 61, 71],
  [6, 17, 26, 35],
  [4, 12, 22, 67],
  [7, 15, 19, 30, 40, 51],
  [0, 16, 24, 29, 46, 58],
  [8, 9, 20, 28, 57, 70],
  [1, 11, 25, 27, 45, 71],
  [2, 10, 18, 50],
  [8, 10, 26, 33, 49, 54],
  [5, 11, 23, 28, 52, 62],
  [4, 14, 20, 30, 45, 63],
  [1, 17, 19, 32, 55, 69],
  [2, 22, 34, 46],
  [7, 13, 29, 42],
  [14, 23, 29, 40, 57, 59],
  [17, 18, 34, 47, 58, 65],
  [9, 26, 31, 52, 55, 68],
  [16, 20, 27, 53, 66, 69],
  [25, 30, 38, 60],
  [12, 33, 39, 51],
  [11, 21, 37, 49],
  [6, 21, 27, 43, 56, 63],
  [8, 18, 32, 44, 53, 67],
  [3, 24, 28, 40, 54, 68],
  [5, 19, 31, 36, 57, 71],
  [0, 35, 41, 61],
  [4, 15, 27, 44, 47, 62],
  [1, 16, 28, 36, 59, 64],
  [3, 9, 32, 45, 50, 65],
  [6, 10, 31, 37, 48, 70],
  [5, 9, 24, 42, 48, 53],
  [3, 15, 20, 36, 43, 55],
  [1, 13, 23, 38, 41, 56],
  [0, 14, 19, 47, 54, 64]
]

set_option maxRecDepth 16000 in
private theorem check2 : complete? (canShare inside2) supportPencils [3, 35] = false := by
  decide +kernel

theorem no_hidden_meeting_2 (Through : ℕ → Prop)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, Through x)
    (pair : ∀ x y, Through x → Through y → canShare inside2 x y = true) :
    ¬ (Through 3 ∧ Through 35) := impossible_of_check _ _ check2 Through cover pair

def inside3 : List (List ℕ) := [
  [37, 43, 52, 56, 59, 61],
  [40, 41, 48, 58, 64, 68],
  [38, 42, 51, 53, 63, 70],
  [36, 44, 47, 55, 69, 71],
  [60, 62, 65, 67],
  [39, 46, 50, 57],
  [45, 49, 54, 66],
  [7, 15, 21, 32, 66, 68],
  [4, 16, 24, 31, 63, 69],
  [8, 12, 23, 34, 61, 70],
  [5, 13, 25, 33, 59, 71],
  [6, 17, 26, 35],
  [3, 14, 22, 64],
  [0, 15, 25, 30, 45, 52],
  [8, 9, 24, 29, 44, 58],
  [2, 16, 20, 28, 40, 70],
  [7, 11, 19, 27, 51, 71],
  [1, 10, 18, 56],
  [4, 13, 19, 34, 52, 58],
  [2, 17, 23, 29, 43, 62],
  [1, 14, 26, 28, 55, 63],
  [8, 11, 20, 32, 42, 69],
  [5, 22, 30, 46],
  [7, 10, 33, 48],
  [16, 26, 30, 37, 49, 60],
  [14, 18, 31, 51, 58, 66],
  [17, 20, 27, 55, 59, 68],
  [9, 21, 33, 52, 57, 69],
  [25, 34, 40, 53],
  [12, 29, 39, 65],
  [11, 23, 38, 47],
  [6, 24, 28, 38, 54, 60],
  [2, 21, 27, 44, 63, 67],
  [8, 19, 31, 36, 56, 68],
  [3, 18, 32, 43, 57, 71],
  [0, 35, 41, 61],
  [4, 15, 28, 36, 51, 59],
  [3, 16, 27, 42, 50, 62],
  [6, 9, 32, 45, 47, 64],
  [1, 13, 31, 37, 44, 70],
  [2, 12, 24, 36, 42, 49],
  [5, 15, 19, 37, 48, 53],
  [0, 13, 21, 43, 50, 55],
  [4, 9, 20, 41, 54, 67]
]

set_option maxRecDepth 16000 in
private theorem check3 : complete? (canShare inside3) supportPencils [2, 35] = false := by
  decide +kernel

theorem no_hidden_meeting_3 (Through : ℕ → Prop)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, Through x)
    (pair : ∀ x y, Through x → Through y → canShare inside3 x y = true) :
    ¬ (Through 2 ∧ Through 35) := impossible_of_check _ _ check3 Through cover pair

end CarterScalesTerminal

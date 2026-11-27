"""Generate the one-file Lean terminal obstruction from the literal matrices."""
from pathlib import Path
import json

from weight16_exact_cover import StartingCase


def rows(values):
    return '[\n  ' + ',\n  '.join('[' + ', '.join(map(str, row)) + ']' for row in values) + '\n]'


base = Path(__file__).parent
saved = json.loads((base/'Case4InsideConfigurations.json').read_text(encoding='utf8'))['0']['inside']
case = StartingCase(0x3da1087)
pencils = [[b for b, edge in enumerate(case.lines) if s in edge] for s in range(16)]
head = '''import Mathlib

/-! Carter's sparse scales case, word `0x3da1087`. For each of the four
enumerated inside configurations, two specified two-secants cannot meet at a
hidden point. The input tables give the two-secants through each support
point and each of the 44 nonhidden exterior points. Their enumeration is a
separate mathematical assertion. The historical search and SAT results are
due to Carter, Lam, Thiel, Swiercz, Bright and coauthors.
-/

namespace CarterScalesTerminal

def supportPencils : List (List ℕ) := '''
body = '''

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

/-- If the listed visible pencils already occur at points different from `p`,
the ordinary uniqueness of line intersections gives the Boolean test above. -/
theorem compatible_of_incidence {Point : Type*} (inc : ℕ → Point → Prop)
    (inside : List (List ℕ)) (p : Point)
    (known : ∀ row ∈ supportPencils ++ inside,
      ∃ q, q ≠ p ∧ ∀ l ∈ row, inc l q)
    (unique : ∀ x y, x ≠ y → ∀ q r, inc x q → inc y q → inc x r → inc y r → q = r) :
    ∀ x y, inc x p → inc y p → canShare inside x y = true := by
  intro x y hx hy
  by_cases hxy : x = y
  · simp [canShare, hxy]
  · have unused : (supportPencils ++ inside).any
          (fun row => row.contains x && row.contains y) = false := by
      cases check : (supportPencils ++ inside).any
          (fun row => row.contains x && row.contains y) with
      | false => rfl
      | true =>
        obtain ⟨row, member, hit⟩ := List.any_eq_true.mp check
        obtain ⟨hitX, hitY⟩ := Bool.and_eq_true_iff.mp hit
        obtain ⟨q, other, atQ⟩ := known row member
        exact False.elim (other (unique x y hxy q p
          (atQ x (List.contains_iff_mem.mp hitX)) (atQ y (List.contains_iff_mem.mp hitY)) hx hy))
    simp [canShare, hxy, unused]
'''
source = head + rows(pencils) + body
for i, record in enumerate(saved):
    b = record['uncovered_B_partners'][0]
    source += f'\ndef inside{i} : List (List ℕ) := '+rows([m for _,m in record['points']])+f'''

set_option maxRecDepth 16000 in
private theorem check{i} : complete? (canShare inside{i}) supportPencils [{b}, 35] = false := by
  decide +kernel

theorem no_hidden_meeting_{i} (Through : ℕ → Prop)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, Through x)
    (pair : ∀ x y, Through x → Through y → canShare inside{i} x y = true) :
    ¬ (Through {b} ∧ Through 35) := impossible_of_check _ _ check{i} Through cover pair

theorem no_hidden_point_{i} {{Point : Type*}} (inc : ℕ → Point → Prop) (p : Point)
    (known : ∀ row ∈ supportPencils ++ inside{i}, ∃ q, q ≠ p ∧ ∀ l ∈ row, inc l q)
    (unique : ∀ x y, x ≠ y → ∀ q r, inc x q → inc y q → inc x r → inc y r → q = r)
    (cover : ∀ pencil ∈ supportPencils, ∃ x ∈ pencil, inc x p) :
    ¬ (inc {b} p ∧ inc 35 p) :=
  no_hidden_meeting_{i} (fun x => inc x p) cover (compatible_of_incidence inc _ p known unique)
'''
source += '\nend CarterScalesTerminal\n'
(base / 'ScalesTerminal.lean').write_bytes(source.encode('utf8'))

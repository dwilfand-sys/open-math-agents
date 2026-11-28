import FormalConjectures.ErdosProblems.«142»

/-! The finite incidence argument for the one-extra-hole prime-power plateau.
An unordered pair of distinct holes is represented exactly once, in increasing
order. Natural-valued labels allow any finite partition of the holes. -/
namespace OMA.R_ResearchErdos142ColumnPairs_R1

def cross {q : ℕ} (label : Fin (q+1) → ℕ) : Finset (Fin (q+1) × Fin (q+1)) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ label e.1 ≠ label e.2)

def H1 : Prop :=
  ∀ (q : ℕ) (label : Fin (q+1) → ℕ) (col : Fin q → Fin (q+1) → Fin q),
    (∀ j, Function.Surjective (col j)) →
    (∀ x y, label x ≠ label y → ∃ j, col j x = col j y) →
    (cross label).card ≤ q ∧
    ((∀ x y, label x = label y) ∨
      ((cross label).card = q ∧ ∃ a : Fin (q+1),
        (∀ x, x ≠ a → label x ≠ label a) ∧
        (∀ x y, x ≠ a → y ≠ a → label x = label y) ∧
        (∀ j x y, x ≠ a → y ≠ a → col j x = col j y → x = y)))

end OMA.R_ResearchErdos142ColumnPairs_R1

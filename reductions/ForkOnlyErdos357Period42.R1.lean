import Mathlib

/- Fork-only specification for a reusable period-42 lemma. -/
namespace Erdos357Period42

def word : Fin 12 → Fin 42 :=
  ![2, 7, 11, 25, 26, 34, 2, 7, 11, 25, 26, 34]

end Erdos357Period42

namespace OMA.R_ForkOnlyErdos357Period42_R1

def H1 : Prop := ∀ (a : ℕ → ℕ), (∀ i : ℕ, (a i : Fin 42) = Erdos357Period42.word (i : Fin 12)) →
  ∀ s h u k : ℕ,
    (∑ j ∈ Finset.range h, a (s + j)) % 42 = (∑ j ∈ Finset.range k, a (u + j)) % 42 →
    h % 12 = k % 12

end OMA.R_ForkOnlyErdos357Period42_R1

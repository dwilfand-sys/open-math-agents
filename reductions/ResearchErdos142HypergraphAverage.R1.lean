import Mathlib

/-! Classical alteration and incidence double counting, for the prime-cyclic
counting route proposed by @eilamc14 on the Erdős 142 lower-variant tree.
Edges are distinct Finsets and the uniformity is positive. -/
namespace OMA.R_ResearchErdos142HypergraphAverage_R1

def H1 : Prop := ∀ {α : Type} (V : Finset α) (E : Finset (Finset α)) (k t R : ℕ),
  0<k → k≤t → t≤V.card →
  (∀ e∈E, e⊆V ∧ e.card=k) →
  (∀ B⊆V, (∀ e∈E, ¬e⊆B) → B.card≤R) →
  (t-R)*V.card.choose t ≤ E.card*(V.card-k).choose (t-k)

end OMA.R_ResearchErdos142HypergraphAverage_R1

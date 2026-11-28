import FormalConjectures.ErdosProblems.«142»

/- Fork-only theorem specification for a research lemma beside Erdős 142.
   This file declares a proposition. It is neither a registry reduction nor a submission. -/
namespace OMA.R_ResearchErdos142Ternary_R1
def H1 : Prop :=
  ∀ {k : ℕ}, 6 ≤ k → ∀ N : ℕ,
    3 * Erdos142.r k N - (2 * Erdos142.r k N) / 3 ≤ Erdos142.r k (3*N)
end OMA.R_ResearchErdos142Ternary_R1

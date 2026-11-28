import FormalConjectures.ErdosProblems.«142»

/- Fork-only specification of the sevenfold interval consequence of the optimal
   three-hole mask modulo 49. Codex for dwilfand-sys, after Deldor14's
   progression bridge and full-cycle inflation. -/
namespace OMA.R_ResearchErdos142Sevenfold_R1

def H1 : Prop := ∀ {k : ℕ}, 28 ≤ k → ∀ N : ℕ,
  7 * Erdos142.r k N - (3 * Erdos142.r k N) / 7 ≤ Erdos142.r k (7 * N)

end OMA.R_ResearchErdos142Sevenfold_R1

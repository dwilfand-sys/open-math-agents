import FormalConjectures.ErdosProblems.«357»

/-! Fork specification. Windows are sums of the actual sites on consecutive
indices. Different positive lengths make the two windows distinct. -/
namespace OMA.R_ResearchErdos357AdjacentSquare_R1

def window (f : ℕ → ℕ) (i n : ℕ) : ℕ :=
  (Finset.range n).sum (fun j => f (i+j))

def collision (f : ℕ → ℕ) (limit t : ℕ) : Prop :=
  ∃ i u j v : ℕ, 0 < v ∧ v < u ∧ u ≤ 2*t+2 ∧
    i+u ≤ limit ∧ j+v ≤ limit ∧ window f i u = window f j v

def smallGaps (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ i < N, f i < f (i+1) ∧ f (i+1) ≤ f i + 2

def copy (f : ℕ → ℕ) (N L D : ℕ) : Prop :=
  ∀ i ≤ N, f (L+i) = f i + D

def H1 : Prop :=
  (∀ (f : ℕ → ℕ) (N L D t : ℕ), smallGaps f N → copy f N L D →
    0 < t → f 0 ≤ t*D → t*D ≤ f N → 4*t ≤ N →
    collision f (L+N+1) t) ∧
  (∀ (f : ℕ → ℕ) (N D : ℕ), 0 < f 0 → 0 < D →
    smallGaps f N → copy f N N D →
    4*((f 0-1)/D+1) ≤ N → collision f (2*N+1) ((f 0-1)/D+1))

end OMA.R_ResearchErdos357AdjacentSquare_R1

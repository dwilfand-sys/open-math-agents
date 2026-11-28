import FormalConjectures.ErdosProblems.«142»

/- Fork research specification for a lower witness at n=116, a universal
   one-point extension bound and the resulting conditional exact value.
   Cariboni tabulated the preceding upper bound for OEIS A003004. -/
namespace OMA.R_ResearchErdos142R5116_R1

def H1 : Prop :=
  68 ≤ Erdos142.r 5 116 ∧
  (∀ k : ℕ, 1 < k → ∀ N : ℕ, Erdos142.r k (N+1) ≤ Erdos142.r k N + 1) ∧
  (Erdos142.r 5 115 ≤ 67 → Erdos142.r 5 116 = 68)

end OMA.R_ResearchErdos142R5116_R1

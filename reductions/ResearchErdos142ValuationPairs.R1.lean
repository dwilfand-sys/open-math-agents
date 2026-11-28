import Mathlib

/-! Counts of ordered pairs in a finite integer interval. The valuation
shell consists of pairs congruent modulo p^e but not modulo p^(e+1). -/
namespace OMA.R_ResearchErdos142ValuationPairs_R1

def pairs (n D : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun z => z.1.val%D=z.2.val%D)

def shell (n p e : ℕ) := pairs n (p^e) \ pairs n (p^(e+1))

def H1 : Prop :=
  (∀ K D : ℕ, (pairs (K*D) D).card = K^2*D) ∧
  (∀ (p e n : ℕ), 0<p → p^(e+1)∣n →
    (shell n p e).card*p^(e+1)=n^2*(p-1)) ∧
  (∀ (p e L q : ℕ), 0<p → p^(e+1)∣L →
    (shell (q*L) p e).card=q^2*(shell L p e).card)

end OMA.R_ResearchErdos142ValuationPairs_R1

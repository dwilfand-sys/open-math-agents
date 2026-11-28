import OMAReductions.R_ResearchErdos142PrimePartialCycle_R1

/- Fork-only composition target for the prime partial-cycle recurrence. -/
namespace OMA.R_ResearchErdos142PrimePartialCycleRecurrence_R1

open Erdos142 OMA.R_ResearchErdos142PrimePartialCycle_R1

def H1 : Prop :=
  OMA.R_ResearchErdos142PrimePartialCycle_R1.H1 →
  OMA.R_ResearchErdos142PrimePartialCycle_R1.H2 →
  OMA.R_ResearchErdos142PrimePartialCycle_R1.H3 →
  OMA.R_ResearchErdos142PrimePartialCycle_R1.H4 →
    ∀ (k p N : ℕ), p.Prime → 2 * p ≤ k →
      (p - 1) * r k N + (r k N ⌈/⌉ p) ≤ r k (p * N)

end OMA.R_ResearchErdos142PrimePartialCycleRecurrence_R1

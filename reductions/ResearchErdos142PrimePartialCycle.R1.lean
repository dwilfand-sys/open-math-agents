import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3

/- Fork-only specification of the prime partial-cycle construction for Erdős 142. -/
namespace OMA.R_ResearchErdos142PrimePartialCycle_R1

open Finset Erdos142

def completeResidues (p : ℕ) : Prop :=
  ∀ a d : ℕ, d % p ≠ 0 → ∃ i < p, (a + i * d) % p = 0

def partialCycle (A : Finset ℕ) (p t : ℕ) : Finset ℕ :=
  ((Ico 1 p).product A).image (fun q => q.1 + p * (q.2 - 1)) ∪
    (A.filter fun x => x % p = t).image (fun x => p * x)

def H1 : Prop :=
  ∀ {A : Finset ℕ} {k p t N : ℕ}, 1 < p → 2 * p ≤ k →
    completeResidues p → A ⊆ Icc 1 N →
    (A : Set ℕ).IsAPOfLengthFree k →
    (partialCycle A p t : Set ℕ).IsAPOfLengthFree k

def H2 : Prop :=
  ∀ {A : Finset ℕ} {p t N : ℕ}, 1 < p → A ⊆ Icc 1 N →
    (partialCycle A p t).card =
      (p - 1) * A.card + (A.filter fun x => x % p = t).card

def H3 : Prop :=
  ∀ (A : Finset ℕ) (p : ℕ), 0 < p →
    ∃ t : Fin p, A.card ≤ p * (A.filter fun x => x % p = t.val).card

end OMA.R_ResearchErdos142PrimePartialCycle_R1

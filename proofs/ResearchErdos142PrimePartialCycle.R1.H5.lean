import OMAReductions.R_ResearchErdos142PrimePartialCycle_R1

/-! Composition of the four checked ingredients into the prime partial-cycle recurrence. -/

namespace Erdos142PrimePartialCycleRecurrence

open Finset Erdos142 OMA.R_ResearchErdos142PrimePartialCycle_R1
  OMA.R_Erdos142_erdos_142_variants_lower_R3

theorem recurrence
    (h1 : H1) (h2 : H2) (h3 : H3) (h4 : H4)
    {k p N : ℕ} (prime : p.Prime) (hk : 2 * p ≤ k) :
    (p - 1) * r k N + (r k N ⌈/⌉ p) ≤ r k (p * N) := by
  have hp1 : 1 < p := prime.one_lt
  obtain ⟨A, hA, freeA, cardA⟩ := exists_maximizer (by omega) N
  obtain ⟨t, ht⟩ := h3 A p prime.pos
  have freeC := h1 hp1 hk (h4 p prime) hA freeA (t := t.val)
  have subsetC : partialCycle A p t.val ⊆ Icc 1 (p * N) := by
    intro z hz
    rw [partialCycle, mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
      obtain ⟨he, hx⟩ := mem_product.mp hq
      have he' := mem_Ico.mp he
      have hx' := mem_Icc.mp (hA hx)
      have hmul := Nat.mul_le_mul_left p (show q.2 - 1 ≤ N - 1 by omega)
      have hsplit : p * N = p * (N - 1) + p := by
        calc
          p * N = p * ((N - 1) + 1) := by congr 1 <;> omega
          _ = p * (N - 1) + p := by ring
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      have hxA := (mem_filter.mp hx).1
      have hx' := mem_Icc.mp (hA hxA)
      exact mem_Icc.mpr
        ⟨Nat.mul_pos prime.pos hx'.1, Nat.mul_le_mul_left p hx'.2⟩
  have hfree : (partialCycle A p t.val : Set ℕ).IsAPOfLengthFree k := freeC
  have hcard := h2 (A := A) (p := p) (t := t.val) (N := N) hp1 hA
  have hceil : A.card ⌈/⌉ p ≤ (A.filter fun x => x % p = t.val).card :=
    (ceilDiv_le_iff_le_mul prime.pos).2 ht
  calc
    (p - 1) * r k N + (r k N ⌈/⌉ p)
        ≤ (p - 1) * A.card + (A.filter fun x => x % p = t.val).card := by
          simpa only [cardA] using Nat.add_le_add_left hceil ((p - 1) * A.card)
    _ = (partialCycle A p t.val).card := hcard.symm
    _ ≤ r k (p * N) := card_le_r subsetC hfree

end Erdos142PrimePartialCycleRecurrence

theorem OMA.solution : OMA.R_ResearchErdos142PrimePartialCycle_R1.H5 := by
  intro h1 h2 h3 h4 k p N prime hk
  exact Erdos142PrimePartialCycleRecurrence.recurrence h1 h2 h3 h4 prime hk

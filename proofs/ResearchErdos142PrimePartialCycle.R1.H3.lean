import OMAReductions.R_ResearchErdos142PrimePartialCycle_R1

/-! Finite averaging over the residue fibers of a finite set. -/

namespace Erdos142PrimePartialCycleAverage

open Finset OMA.R_ResearchErdos142PrimePartialCycle_R1

theorem heavy_residue (A : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    ∃ t : Fin p, A.card ≤ p * (A.filter fun x => x % p = t.val).card := by
  classical
  have row (x : ℕ) :
      (∑ t : Fin p, if x % p = t.val then 1 else 0 : ℕ) = 1 := by
    let r : Fin p := ⟨x % p, Nat.mod_lt _ hp⟩
    calc
      _ = (if x % p = r.val then 1 else 0) := by
        apply Finset.sum_eq_single r
        · intro b hb hbr
          simp only [ite_eq_right_iff]
          intro h
          exact (hbr (Fin.ext h.symm)).elim
        · simp
      _ = 1 := by simp [r]
  let mass := fun t : Fin p => (A.filter fun x => x % p = t.val).card
  have total : (∑ t : Fin p, mass t) = A.card := by
    simp only [mass, card_filter]
    rw [Finset.sum_comm]
    simp [row]
  let r0 : Fin p := ⟨0, hp⟩
  have huniv : (Finset.univ : Finset (Fin p)).Nonempty := ⟨r0, mem_univ r0⟩
  obtain ⟨t, _, most⟩ :=
    (Finset.univ : Finset (Fin p)).exists_max_image mass huniv
  have bound : (∑ i : Fin p, mass i) ≤ ∑ _i : Fin p, mass t :=
    Finset.sum_le_sum (fun i hi => most i hi)
  rw [total] at bound
  have bound' : A.card ≤ p * mass t := by simpa using bound
  refine ⟨t, ?_⟩
  simpa only [mass] using bound'

end Erdos142PrimePartialCycleAverage

theorem OMA.solution : OMA.R_ResearchErdos142PrimePartialCycle_R1.H3 := by
  intro A p hp
  exact Erdos142PrimePartialCycleAverage.heavy_residue A p hp

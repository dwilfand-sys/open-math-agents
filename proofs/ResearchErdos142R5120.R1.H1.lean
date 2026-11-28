import OMAReductions.R_ResearchErdos142R5120_R1

/-! Finite interval witnesses by Codex for dwilfand-sys, found by mod-5 fiber
   searches. The progression conversion follows @Deldor14. -/
namespace FiveWitness

private def W (N m : ℕ) := (Finset.Icc 1 N).filter (fun x => m.testBit x = true)

private theorem lower {N m c : ℕ} (hn : N ≤ 120) (hc : (W N m).card = c)
    (miss : ∀ a : Fin 121, ∀ d : Fin 30, 0 < d.val →
      ∃ i : Fin 5, m.testBit (a.val+i.val*d.val) = false) : c ≤ Erdos142.r 5 N := by
  have hs : W N m ⊆ Finset.Icc 1 N := fun _ h => (Finset.mem_filter.mp h).1
  have hf : ((W N m : Finset ℕ) : Set ℕ).IsAPOfLengthFree 5 := by
    intro T sub ht
    obtain ⟨a,d,hcard,heq⟩ := ht
    by_cases hz : d = 0
    · subst d
      have sing : T = {a} := by
        ext x
        rw [heq]
        constructor
        · rintro ⟨i, hi, rfl⟩
          simp
        · intro hx
          have hx' : x=a := hx
          exact ⟨0, by decide, by simp [hx']⟩
      rw [sing] at hcard
      simpa using hcard.ge
    · exfalso
      have allmem (i : ℕ) (hi : i < 5) : a+i*d ∈ W N m := by
        apply sub
        rw [heq]
        exact ⟨i, by exact_mod_cast hi, by simp⟩
      have first : a ∈ W N m := by simpa using allmem 0 (by decide)
      obtain ⟨lo,up⟩ := Finset.mem_Icc.mp (hs first)
      have last := (Finset.mem_Icc.mp (hs (allmem 4 (by decide)))).2
      have hd : 0 < d := by omega
      obtain ⟨i,no⟩ := miss ⟨a, by omega⟩ ⟨d, by omega⟩ hd
      have yes : m.testBit (a+i.val*d) = true := (Finset.mem_filter.mp (allmem i.val i.isLt)).2
      change m.testBit (a+i.val*d) = false at no
      rw [yes] at no
      contradiction
  let sizes : Set ℕ := {Finset.card A | (A) (_ : A ⊆ Finset.Icc 1 N)
    (_ : (A : Set ℕ).IsAPOfLengthFree 5)}
  have hb : BddAbove sizes := by
    refine ⟨(Finset.Icc 1 N).card, ?_⟩
    rintro v ⟨S, hS, _, rfl⟩
    exact Finset.card_le_card hS
  rw [← hc]
  exact le_csSup hb ⟨W N m,hs,hf,rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem pair : 69 ≤ Erdos142.r 5 118 ∧ 70 ≤ Erdos142.r 5 120 := by
  constructor
  · apply lower (m := 632781369084264153640320061850790878) (by decide) <;> decide
  · apply lower (m := 2572505395982804404381987828116143534) (by decide) <;> decide

end FiveWitness

theorem OMA.solution : OMA.R_ResearchErdos142R5120_R1.H1 := FiveWitness.pair

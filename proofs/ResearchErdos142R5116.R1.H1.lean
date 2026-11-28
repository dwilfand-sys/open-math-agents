import OMAReductions.R_ResearchErdos142R5116_R1

/- Codex for dwilfand-sys. The explicit witness was found by a Codex worker
   searching residue-class profiles. Deldor14 supplied the original interval
   extremizer and progression bridge used by fork #75, reused below.
   Fausto A. C. Cariboni lists r_5(115) = 67 in OEIS A003004.
   That predecessor bound is an explicit hypothesis of the equality below. -/

namespace OMAR5116

private def Free (S : Set ℕ) (k : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i*d ∈ S

private theorem free_iff (S : Set ℕ) {k : ℕ} (hk : 1 < k) :
    S.IsAPOfLengthFree (k : ℕ∞) ↔ Free S k := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · intro h a d hd all_mem
    let f : Fin k → ℕ := fun i => a + (i : ℕ)*d
    have inj : Function.Injective f := by
      intro i j eq
      apply Fin.ext
      have eq' : a+(i : ℕ)*d = a+(j : ℕ)*d := eq
      exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel eq')
    have sub : Set.range f ⊆ S := by
      rintro x ⟨i, rfl⟩
      exact all_mem i i.isLt
    apply (not_le_of_gt hk') (h (Set.range f) sub ?_)
    refine ⟨a,d,?_,?_⟩
    · rw [← ENat.card_congr (Equiv.ofInjective f inj)]
      simp [ENat.card_eq_coe_fintype_card]
    · ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(i : ℕ), by exact_mod_cast i.isLt, by simp [f]⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, by exact_mod_cast hi⟩, by simp [f]⟩
  · intro hf T sub ht
    obtain ⟨a,d,hcard,heq⟩ := ht
    by_cases zero : d=0
    · subst d
      have sing : T = {a} := by
        ext x
        rw [heq]
        constructor
        · rintro ⟨i, hi, rfl⟩
          simp
        · intro hx
          have hx' : x=a := hx
          exact ⟨0, by exact_mod_cast (show 0<k by omega), by simp [hx']⟩
      rw [sing] at hcard
      simpa using hcard.ge
    · exfalso
      apply hf a d (by omega)
      intro i hi
      apply sub
      rw [heq]
      exact ⟨i, by exact_mod_cast hi, by simp⟩

private abbrev sizes (k N : ℕ) : Set ℕ :=
  {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}

private theorem bounded (k N : ℕ) : BddAbove (sizes k N) := by
  refine ⟨(Finset.Icc 1 N).card, ?_⟩
  rintro m ⟨S, hs, _, rfl⟩
  exact Finset.card_le_card hs

private theorem attained {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ Free (S : Set ℕ) k ∧
      S.card = Erdos142.r k N := by
  have emptyFree : Free ((∅ : Finset ℕ) : Set ℕ) k := by
    intro a d _ h
    exact Finset.notMem_empty _ (h 0 (by omega))
  have hn : (sizes k N).Nonempty :=
    ⟨0,∅,Finset.empty_subset _, (free_iff _ hk).mpr emptyFree, rfl⟩
  obtain ⟨S, hsub, hf, he⟩ := Nat.sSup_mem hn (bounded k N)
  exact ⟨S,hsub,(free_iff _ hk).mp hf,he⟩

private theorem bound_witness {k q : ℕ} (hk : 1<k) (A : Finset ℕ)
    (hs : A ⊆ Finset.Icc 1 q) (hf : Free (A : Set ℕ) k) : A.card ≤ Erdos142.r k q :=
  le_csSup (bounded k q) ⟨A,hs,(free_iff _ hk).mpr hf,rfl⟩

/- Bit n is set precisely for the following sites:
   1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 18, 20, 21, 22, 25, 35,
   37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 56, 60, 65, 66,
   68, 70, 71, 72, 73, 75, 76, 77, 78, 81, 82, 85, 87, 88, 90, 91, 93, 95,
   96, 97, 100, 101, 102, 103, 106, 107, 108, 110, 112, 113, 115, 116. -/
private def witnessMask : ℕ := 142077303049640450955124154001816542

private def W : Finset ℕ :=
  (Finset.Icc 1 116).filter (fun n => witnessMask.testBit n = true)

private theorem sizeW : W.card = 68 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem misses : ∀ a : Fin 117, ∀ d : Fin 29, 0 < d.val →
    ∃ i : Fin 5, witnessMask.testBit (a.val + i.val*d.val) = false := by
  decide

private theorem subsetW : W ⊆ Finset.Icc 1 116 := fun _ h => (Finset.mem_filter.mp h).1

private theorem freeW : Free (W : Set ℕ) 5 := by
  intro a d hd h
  have first : a ∈ W := by simpa using h 0 (by decide)
  have last : a+4*d ∈ W := h 4 (by decide)
  have ha := (Finset.mem_Icc.mp (subsetW first)).2
  have endpt := (Finset.mem_Icc.mp (subsetW last)).2
  obtain ⟨i, no⟩ := misses ⟨a, by omega⟩ ⟨d, by omega⟩ hd
  have yes : witnessMask.testBit (a+i.val*d) = true :=
    (Finset.mem_filter.mp (h i.val i.isLt)).2
  change witnessMask.testBit (a+i.val*d) = false at no
  rw [yes] at no
  contradiction

private theorem lower : 68 ≤ Erdos142.r 5 116 := by
  have hb := bound_witness (by decide : 1 < 5) W subsetW freeW
  rwa [sizeW] at hb

private theorem extension (k : ℕ) (hk : 1 < k) (N : ℕ) :
    Erdos142.r k (N+1) ≤ Erdos142.r k N + 1 := by
  classical
  obtain ⟨A, ha, hf, size⟩ := attained hk (N+1)
  let T := A.erase (N+1)
  have sub : T ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨hne, hA⟩ := Finset.mem_erase.mp hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp (ha hA)
    exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have kept : Free (T : Set ℕ) k := by
    intro a d hd h
    exact hf a d hd (fun i hi => (Finset.mem_erase.mp (h i hi)).2)
  have hb := bound_witness hk T sub kept
  have loss : A.card - 1 ≤ T.card := Finset.pred_card_le_card_erase
  omega

end OMAR5116

theorem OMA.solution : OMA.R_ResearchErdos142R5116_R1.H1 := by
  refine ⟨OMAR5116.lower, OMAR5116.extension, ?_⟩
  intro h
  have lower := OMAR5116.lower
  have upper : Erdos142.r 5 116 ≤ Erdos142.r 5 115 + 1 :=
    OMAR5116.extension 5 (by decide) 115
  omega

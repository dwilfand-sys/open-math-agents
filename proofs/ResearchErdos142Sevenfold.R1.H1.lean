import OMAReductions.R_ResearchErdos142Sevenfold_R1
import Mathlib.Combinatorics.Pigeonhole

/-!
The interval extremizer and progression bridge below are adapted from Deldor14's
`research/erdos142-parity/{UpstreamParity,Doubling,PrimePower}.lean`, commit
be8d1d53627bbd7359a67b881d6ab1829f75a206. Deldor14's full-cycle prime-power
inflation inspired the construction. The ternary bound was checked in fork #75. The three-hole mask modulo 49 was
checked in fork #76. This file proves its sevenfold interval consequence using
six full digit fibers and an averaged translate of four residue classes.
-/

namespace OMASevenfold

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

private def allowed (r t : ℕ) : Bool :=
  decide ((r+t)%7 ≠ 0 ∧ (r+t)%7 ≠ 1 ∧ (r+t)%7 ≠ 3)

private def keep (x : ℕ) (t : Fin 7) : Bool := allowed (x%7) t.val

private theorem heavy (A : Finset ℕ) :
    ∃ t : Fin 7, 7*A.card - (3*A.card)/7 ≤
      6*A.card + (A.filter (fun x => keep x t = true)).card := by
  classical
  have row0 : ∀ r : Fin 7, (∑ t : Fin 7, if allowed r.val t.val = true then 1 else 0 : ℕ) = 4 := by
    decide
  have row (x : ℕ) : (∑ t : Fin 7, if keep x t = true then 1 else 0 : ℕ) = 4 :=
    row0 ⟨x%7, Nat.mod_lt _ (by decide)⟩
  let mass := fun t : Fin 7 => (A.filter (fun x => keep x t = true)).card
  have total : (∑ t : Fin 7, mass t) = 4*A.card := by
    simp only [mass, Finset.card_filter]
    rw [Finset.sum_comm]
    simp [row, Nat.mul_comm]
  obtain ⟨t, _, most⟩ := (Finset.univ : Finset (Fin 7)).exists_max_image mass Finset.univ_nonempty
  have bound : (∑ i : Fin 7, mass i) ≤ ∑ _ : Fin 7, mass t :=
    Finset.sum_le_sum (fun i hi => most i hi)
  rw [total] at bound
  have bound' : 4*A.card ≤ 7*mass t := by simpa using bound
  change 4*A.card ≤ 7*(A.filter (fun x => keep x t = true)).card at bound'
  exact ⟨t, by omega⟩

private def block (p : ℕ × ℕ) : ℕ := 7*(p.1-1) + p.2 + 1

private theorem decode {x j : ℕ} (hx : 1 ≤ x) (hj : j < 7) :
    (block (x,j)-1)/7+1=x ∧ (block (x,j)-1)%7=j := by
  dsimp [block]
  omega

/-- The seven translates of the three-hole mask 0,7,21 mod 49.
The point is tested on the full finite residue classes by kernel reduction. -/
set_option maxHeartbeats 28000000 in
set_option maxRecDepth 150000 in
private theorem hits : ∀ a d : Fin 49, d.val % 7 ≠ 0 → ∀ t : Fin 7,
    ∃ j : Fin 28, let v := (a.val+j.val*d.val)%49
                  v%7 = 0 ∧ keep (v/7) t = false := by
  decide

private theorem normmod (a d i : ℕ) :
    (a%49 + i*(d%49))%49 = (a+i*d)%49 := by
  calc
    _ = (a%49%49 + (i*(d%49))%49)%49 := Nat.add_mod _ _ _
    _ = (a%49 + ((i%49)*(d%49))%49)%49 := by
      rw [Nat.mul_mod i (d%49)]; simp only [Nat.mod_mod]
    _ = (a%49 + (i*d)%49)%49 := by rw [Nat.mul_mod i d]
    _ = _ := (Nat.add_mod _ _ _).symm

private theorem step_seven {a d : ℕ} (t : Fin 7)
    (mask : ∀ i < 28, (a+i*d)%7=0 → keep ((a+i*d)/7) t = true) : 7 ∣ d := by
  by_contra hd
  have u : d % 7 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
  let ar : Fin 49 := ⟨a%49, Nat.mod_lt _ (by decide)⟩
  let dr : Fin 49 := ⟨d%49, Nat.mod_lt _ (by decide)⟩
  have du : dr.val%7 ≠ 0 := by change d%49%7 ≠ 0; omega
  obtain ⟨j, h0, h1⟩ := hits ar dr du t
  change ((a%49+j.val*(d%49))%49)%7 = 0 at h0
  change keep (((a%49+j.val*(d%49))%49)/7) t = false at h1
  rw [normmod] at h0 h1
  let v := a+j.val*d
  change (v%49)%7 = 0 at h0
  change keep ((v%49)/7) t = false at h1
  have hv : v%7 = 0 := by omega
  have yes := mask j.val j.isLt hv
  change allowed ((v/7)%7) t.val = true at yes
  change allowed (((v%49)/7)%7) t.val = false at h1
  have same : ((v%49)/7)%7 = (v/7)%7 := by omega
  rw [same, yes] at h1
  contradiction

/-- The three-hole mask modulo 49 gives the sevenfold interval construction. -/
theorem sevenfold_dilation {k : ℕ} (hk : 28 ≤ k) (N : ℕ) :
    7 * Erdos142.r k N - (3 * Erdos142.r k N) / 7 ≤ Erdos142.r k (7*N) := by
  classical
  obtain ⟨A,ha,hf,hc⟩ := attained (by omega : 1 < k) N
  obtain ⟨t, rich⟩ := heavy A
  let B := A.filter (fun x => keep x t = true)
  let D := (A ×ˢ Finset.range 6) ∪ (B ×ˢ ({6} : Finset ℕ))
  let C := D.image block
  have info {x j : ℕ} (h : (x,j) ∈ D) :
      x ∈ A ∧ j < 7 ∧ (j = 6 → keep x t = true) := by
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨hA,hj⟩ := Finset.mem_product.mp h
      have hj' := Finset.mem_range.mp hj
      exact ⟨hA,by omega,by omega⟩
    · obtain ⟨hB,hj⟩ := Finset.mem_product.mp h
      obtain ⟨hA,ht⟩ := Finset.mem_filter.mp hB
      have hj' := Finset.mem_singleton.mp hj
      exact ⟨hA,by omega,fun _ => ht⟩
  have dis : Disjoint (A ×ˢ Finset.range 6) (B ×ˢ ({6} : Finset ℕ)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨x,j⟩ hl hr
    have h₁ := Finset.mem_range.mp (Finset.mem_product.mp hl).2
    have h₂ := Finset.mem_singleton.mp (Finset.mem_product.mp hr).2
    omega
  have cardC : C.card = 6*A.card + B.card := by
    change (D.image block).card = _
    rw [Finset.card_image_of_injOn]
    · dsimp only [D]
      rw [Finset.card_union_of_disjoint dis, Finset.card_product, Finset.card_product,
        Finset.card_range, Finset.card_singleton, Nat.mul_one, Nat.mul_comm A.card 6]
    · rintro ⟨x,j⟩ hx ⟨y,l⟩ hy he
      have ix := info hx
      have iy := info hy
      have dx := decode (Finset.mem_Icc.mp (ha ix.1)).1 ix.2.1
      have dy := decode (Finset.mem_Icc.mp (ha iy.1)).1 iy.2.1
      exact Prod.ext
        (dx.1.symm.trans ((congrArg (fun z => (z-1)/7+1) he).trans dy.1))
        (dx.2.symm.trans ((congrArg (fun z => (z-1)%7) he).trans dy.2))
  have point {z : ℕ} (hz : z ∈ C) :
      z ∈ Finset.Icc 1 (7*N) ∧ (z-1)/7+1 ∈ A ∧ (z%7=0 → keep (z/7) t = true) := by
    obtain ⟨⟨x,j⟩,hj,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hA,jlt,rest⟩ := info hj
    obtain ⟨xlo,xhi⟩ := Finset.mem_Icc.mp (ha hA)
    have dec := (decode xlo jlt).1
    refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · dsimp [block]; omega
    · dsimp [block]; omega
    · rw [dec]
      exact hA
    · dsimp [block]
      intro divisible
      have hj6 : j = 6 := by omega
      have hd : (7*(x-1)+j+1)/7 = x := by omega
      rw [hd]
      exact rest hj6
  have freeC : Free (C : Set ℕ) k := by
    intro a d hd all_mem
    have div := step_seven (a:=a) (d:=d) t
      (fun i hi => (point (all_mem i (by omega))).2.2)
    obtain ⟨e,rfl⟩ := div
    have first : a ∈ C := by simpa using all_mem 0 (by omega)
    have apos := (Finset.mem_Icc.mp (point first).1).1
    apply hf ((a-1)/7+1) e (by omega)
    intro i hi
    have val := (point (all_mem i hi)).2.1
    have id : a+i*(7*e)-1 = a-1+7*(i*e) := by
      rw [Nat.mul_left_comm i 7 e]
      omega
    rw [id, Nat.add_mul_div_left _ _ (by decide : 0 < 7)] at val
    rwa [show (a-1)/7+1+i*e=(a-1)/7+i*e+1 by omega]
  have upper := bound_witness (by omega : 1 < k) C (fun _ h => (point h).1) freeC
  rw [cardC] at upper
  rw [← hc]
  exact le_trans rich upper

end OMASevenfold

theorem OMA.solution : OMA.R_ResearchErdos142Sevenfold_R1.H1 := by
  intro k hk N
  exact OMASevenfold.sevenfold_dilation hk N

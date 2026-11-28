import OMAReductions.R_ResearchErdos142ColumnPairs_R1
import Mathlib

/-! The proof uses ordered representatives of unordered pairs, a single-point
deletion in each column, and an injection of pairs into their witness columns. -/
namespace ColumnPairs
open OMA.R_ResearchErdos142ColumnPairs_R1

private def pair {n : ℕ} (x y : Fin n) : Fin n × Fin n :=
  if x < y then (x,y) else (y,x)

private theorem pair_eq {n : ℕ} {a b x y : Fin n} (h : pair a b = pair x y) :
    (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
  by_cases hab : a < b <;> by_cases hxy : x < y <;>
    simp [pair,hab,hxy] at h <;> tauto

private theorem pair_mem {q : ℕ} (c : Fin (q+1) → ℕ) {x y : Fin (q+1)}
    (ne : c x ≠ c y) : pair x y ∈ cross c := by
  by_cases h : x < y
  · simp [pair,h,cross,ne]
  · have xy : x ≠ y := fun he => ne (congrArg c he)
    have hy : y < x := by omega
    simp [pair,h,cross,hy,Ne.symm ne]

private theorem col_unique {q : ℕ} (f : Fin (q+1) → Fin q)
    (onto : Function.Surjective f) {x y z w : Fin (q+1)}
    (xy : x < y) (zw : z < w) (eq : f x = f y) (eq' : f z = f w) :
    x=z ∧ y=w := by
  classical
  let S := (Finset.univ : Finset (Fin (q+1))).erase x
  have img : S.image f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨u,hu⟩ := onto v
    by_cases ux : u=x
    · subst u
      exact Finset.mem_image.mpr ⟨y,by simp [S,ne_of_gt xy],eq.symm.trans hu⟩
    · exact Finset.mem_image.mpr ⟨u,by simp [S,ux],hu⟩
  have hcard : S.card = q := by simp [S, Finset.card_erase_of_mem]
  have hinj : Set.InjOn f (S : Set (Fin (q+1))) := Finset.card_image_iff.mp (by
    rw [img,hcard]; simp)
  have away {u v : Fin (q+1)} (hu : u ≠ x) (hv : v ≠ x) (h : f u=f v) : u=v :=
    hinj (by simpa [S] using hu) (by simpa [S] using hv) h
  by_cases zx : z=x
  · subst z
    exact ⟨rfl,away (ne_of_gt xy) (ne_of_gt zw) (eq.symm.trans eq')⟩
  · by_cases wx : w=x
    · subst w
      have bad := away zx (ne_of_gt xy) (eq'.trans eq)
      omega
    · have bad := away zx wx eq'
      omega

private theorem partition_product {q : ℕ} (c : Fin (q+1) → ℕ)
    (S T : Finset (Fin (q+1))) (sep : ∀ x ∈ S, ∀ y ∈ T, c x ≠ c y) :
    S.card*T.card ≤ (cross c).card := by
  classical
  calc
    S.card*T.card = (S ×ˢ T).card := by simp
    _ ≤ (cross c).card := by
      apply Finset.card_le_card_of_injOn (fun e => pair e.1 e.2)
      · intro e he
        obtain ⟨hs,ht⟩ := Finset.mem_product.mp he
        exact pair_mem c (sep _ hs _ ht)
      · intro u hu v hv he
        obtain ⟨us,ut⟩ := Finset.mem_product.mp hu
        obtain ⟨vs,vt⟩ := Finset.mem_product.mp hv
        rcases pair_eq he with h|h
        · exact Prod.ext h.1 h.2
        · exact ((sep _ us _ vt) (congrArg c h.1)).elim

theorem count_and_classify : H1 := by
  classical
  intro q c f onto meet
  have ed (e : ↥(cross c)) : e.val.1 < e.val.2 ∧ c e.val.1 ≠ c e.val.2 :=
    (Finset.mem_filter.mp e.property).2
  let pick (e : ↥(cross c)) : Fin q := Classical.choose (meet _ _ (ed e).2)
  have hp (e : ↥(cross c)) : f (pick e) e.val.1 = f (pick e) e.val.2 :=
    Classical.choose_spec (meet _ _ (ed e).2)
  have pinj : Function.Injective pick := by
    intro e v he
    have same := hp v
    rw [←he] at same
    have h := col_unique _ (onto (pick e)) (ed e).1 (ed v).1 (hp e) same
    exact Subtype.ext (Prod.ext h.1 h.2)
  have cap : (cross c).card ≤ q := by
    simpa using Fintype.card_le_of_injective pick pinj
  refine ⟨cap, ?_⟩
  by_cases singleton : ∃ a : Fin (q+1), ∀ x, x ≠ a → c x ≠ c a
  · obtain ⟨a, alone⟩ := singleton
    let spokes := ((Finset.univ : Finset (Fin (q+1))).erase a).image (pair a)
    have spoke_inj : Function.Injective (pair a) := by
      intro x y he
      rcases pair_eq he with h|h
      · exact h.2
      · exact h.2.trans h.1
    have spoke_card : spokes.card=q := by
      dsimp [spokes]
      rw [Finset.card_image_of_injective _ spoke_inj]
      simp [Finset.card_erase_of_mem]
    have sub : spokes ⊆ cross c := by
      intro e h
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      exact pair_mem c (Ne.symm (alone x (Finset.mem_erase.mp hx).1))
    have se : spokes = cross c := Finset.eq_of_subset_of_card_le sub (by omega)
    have size : (cross c).card=q := se ▸ spoke_card
    have same : ∀ x y, x ≠ a → y ≠ a → c x=c y := by
      intro x y hx hy
      by_contra hn
      have e := pair_mem c hn
      rw [←se] at e
      obtain ⟨u,_,he⟩ := Finset.mem_image.mp e
      rcases pair_eq he with h|h
      · exact hx h.1.symm
      · exact hy h.1.symm
    right
    refine ⟨size, a, alone, same, ?_⟩
    have used : (Finset.univ : Finset ↥(cross c)).image pick = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injective _ pinj]
      simp [size]
    intro j x y hx hy hxy
    have hj : j ∈ (Finset.univ : Finset ↥(cross c)).image pick := by rw [used]; simp
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hj
    have eEq := hp e
    rw [he] at eEq
    rcases lt_trichotomy x y with ord|eq|ord
    · have m := col_unique _ (onto j) (ed e).1 ord eEq hxy
      exact ((ed e).2 (same _ _ (by rwa [m.1]) (by rwa [m.2]))).elim
    · exact eq
    · have m := col_unique _ (onto j) (ed e).1 ord eEq hxy.symm
      exact ((ed e).2 (same _ _ (by rwa [m.1]) (by rwa [m.2]))).elim
  · left
    push Not at singleton
    intro a b
    by_contra hn
    let S := (Finset.univ : Finset (Fin (q+1))).filter (fun x => c x = c a)
    let T := (Finset.univ : Finset (Fin (q+1))) \ S
    have A (x : Fin (q+1)) : x ∈ S ↔ c x = c a := by simp [S]
    have B (x : Fin (q+1)) : x ∈ T ↔ c x ≠ c a := by simp [T,S]
    obtain ⟨u,hu,cu⟩ := singleton a
    obtain ⟨v,hv,cv⟩ := singleton b
    have bigS : 1 < S.card := Finset.one_lt_card.mpr
      ⟨a, (A a).2 rfl, u, (A u).2 cu, Ne.symm hu⟩
    have bigT : 1 < T.card := Finset.one_lt_card.mpr
      ⟨b, (B b).2 (Ne.symm hn), v, (B v).2 (fun he => hn (he.symm.trans cv)), Ne.symm hv⟩
    have prodBound := partition_product c S T (by
      intro x hx y hy eq
      exact (B y).1 hy (eq.symm.trans ((A x).1 hx)))
    have count : T.card + S.card = q+1 := by
      have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      simpa [T] using hc
    have hs := Nat.mul_le_mul_left S.card (show 2 ≤ T.card by omega)
    have ht := Nat.mul_le_mul_right T.card (show 2 ≤ S.card by omega)
    omega

end ColumnPairs

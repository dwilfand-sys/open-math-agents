import OMAReductions.R_Erdos963_erdos_963_parts_ii_R1
import Mathlib.Tactic

/-!
The affine-seven classification comes from the public affine-fourteen notes
for Erdős problem 963, as cited by @MrSeizy in the parent reduction #8664.
https://erdosproblems.ai/wiki/research/erdos_963/affine_fourteen

In a five-set, two distinct disjoint equal-cardinality subsets with the same
sum must be pairs. Among four ordered integers the outer pair must then sum
to the inner pair. We use these five-way alternatives on the ordered seven
points to prove central symmetry and one relation between their radii.
-/

namespace Erdos963Seven

private def Affine (M : Finset ℤ) : Prop :=
  ∀ T ⊆ M, ∀ S ⊆ M, Disjoint T S → T.card = S.card → T.sum id = S.sum id → T = S

private theorem fiveCard {a b c d e : ℤ} (ab : a < b) (bc : b < c) (cd : c < d) (de : d < e) :
    ({a,b,c,d,e} : Finset ℤ).card = 5 := by
  simp [show a ≠ b by omega, show a ≠ c by omega, show a ≠ d by omega,
    show a ≠ e by omega, show b ≠ c by omega, show b ≠ d by omega,
    show b ≠ e by omega, show c ≠ d by omega, show c ≠ e by omega, show d ≠ e by omega]

set_option maxHeartbeats 4000000 in
private theorem fiveCollision {a b c d e : ℤ} (ab : a < b) (bc : b < c)
    (cd : c < d) (de : d < e) (bad : ¬ Affine {a,b,c,d,e}) :
    a+d=b+c ∨ a+e=b+c ∨ a+e=b+d ∨ a+e=c+d ∨ b+e=c+d := by
  by_contra! no
  apply bad
  intro T hT S hS hdis hcard hsum
  have bound := Finset.card_le_card (Finset.union_subset hT hS)
  rw [Finset.card_union_of_disjoint hdis, fiveCard ab bc cd de] at bound
  rcases (show T.card = 0 ∨ T.card = 1 ∨ T.card = 2 by omega) with hz | ho | ht
  · exact (Finset.card_eq_zero.mp hz).trans (Finset.card_eq_zero.mp (hcard.symm.trans hz)).symm
  · have hs := hcard.symm.trans ho
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp ho
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs
    have eq : u = v := by simpa using hsum
    rw [eq]
  · have hs := hcard.symm.trans ht
    obtain ⟨p,q,hpq,rfl⟩ := Finset.card_eq_two.mp ht
    obtain ⟨r,s,hrs,rfl⟩ := Finset.card_eq_two.mp hs
    have psum : p+q = r+s := by simpa [hpq, hrs] using hsum
    have cross {u v : ℤ} (hu : u ∈ ({p,q} : Finset ℤ)) (hv : v ∈ ({r,s} : Finset ℤ)) : u ≠ v := by
      intro eq
      subst v
      exact Finset.disjoint_left.mp hdis hu hv
    have pr : p ≠ r := cross (by simp) (by simp)
    have ps : p ≠ s := cross (by simp) (by simp)
    have qr : q ≠ r := cross (by simp) (by simp)
    have qs : q ≠ s := cross (by simp) (by simp)
    have pm := hT (show p ∈ ({p,q} : Finset ℤ) by simp)
    have qm := hT (show q ∈ ({p,q} : Finset ℤ) by simp)
    have rm := hS (show r ∈ ({r,s} : Finset ℤ) by simp)
    have sm := hS (show s ∈ ({r,s} : Finset ℤ) by simp)
    simp only [Finset.mem_insert,Finset.mem_singleton] at pm qm rm sm
    exfalso
    rcases pm with h|h|h|h|h <;> subst p
    all_goals
      rcases qm with h|h|h|h|h <;> subst q <;> try contradiction
    all_goals
      rcases rm with h|h|h|h|h <;> subst r <;> try contradiction
    all_goals
      rcases sm with h|h|h|h|h <;> subst s <;> first | contradiction | omega

/-- The four linear conclusions express two facts. The ordered set is
centrally symmetric, and its largest radius is the sum of the other two. -/
set_option maxHeartbeats 14000000 in
private theorem orderedSeven (f : Fin 7 → ℤ) (mono : StrictMono f)
    (hit : ∀ a b c d e : Fin 7, a < b → b < c → c < d → d < e →
      f a+f d=f b+f c ∨ f a+f e=f b+f c ∨ f a+f e=f b+f d ∨
      f a+f e=f c+f d ∨ f b+f e=f c+f d) :
    f 0+f 6 = 2*f 3 ∧ f 1+f 5 = 2*f 3 ∧ f 2+f 4 = 2*f 3 ∧ f 0+f 3 = f 1+f 2 := by
  have s01 := mono (show (0 : Fin 7) < 1 by decide)
  have s12 := mono (show (1 : Fin 7) < 2 by decide)
  have s23 := mono (show (2 : Fin 7) < 3 by decide)
  have s34 := mono (show (3 : Fin 7) < 4 by decide)
  have s45 := mono (show (4 : Fin 7) < 5 by decide)
  have s56 := mono (show (5 : Fin 7) < 6 by decide)
  by_contra! fails
  rcases hit 0 1 2 3 4 (by decide) (by decide) (by decide) (by decide) with h0 | h0 | h0 | h0 | h0
  · rcases hit 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · omega
    · omega
    · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
      · rcases hit 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
    · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · omega
  · rcases hit 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · omega
    · omega
    · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
      · rcases hit 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
    · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · omega
      · omega
    · rcases hit 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · omega
      · omega
      · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
  · rcases hit 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · rcases hit 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · rcases hit 0 1 2 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
          · omega
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
    · omega
    · omega
    · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
      · omega
      · omega
      · omega
      · omega
    · rcases hit 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases hit 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
      · omega
      · omega
  · rcases hit 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · rcases hit 0 1 2 4 5 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · omega
      · omega
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · rcases hit 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases hit 0 1 3 4 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
        · omega
        · omega
    · omega
    · omega
    · omega
    · omega
  · rcases hit 1 2 3 5 6 (by decide) (by decide) (by decide) (by decide) with h1 | h1 | h1 | h1 | h1
    · omega
    · omega
    · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases hit 0 1 2 3 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases hit 0 2 3 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · omega
        · omega
        · omega
        · omega
      · omega
      · omega
      · omega
    · rcases hit 0 1 3 5 6 (by decide) (by decide) (by decide) (by decide) with h2 | h2 | h2 | h2 | h2
      · rcases hit 0 2 3 4 5 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · rcases hit 0 1 2 3 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · rcases hit 0 2 4 5 6 (by decide) (by decide) (by decide) (by decide) with h5 | h5 | h5 | h5 | h5
            · omega
            · omega
            · omega
            · omega
            · omega
          · omega
      · rcases hit 0 1 4 5 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · omega
        · omega
      · rcases hit 0 1 2 4 6 (by decide) (by decide) (by decide) (by decide) with h3 | h3 | h3 | h3 | h3
        · omega
        · omega
        · omega
        · rcases hit 0 3 4 5 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
        · rcases hit 0 1 3 4 6 (by decide) (by decide) (by decide) (by decide) with h4 | h4 | h4 | h4 | h4
          · omega
          · omega
          · omega
          · omega
          · omega
      · omega
      · omega

end Erdos963Seven

open Erdos963Seven

theorem OMA.solution : OMA.R_Erdos963_erdos_963_parts_ii_R1.H3 := by
  classical
  change ∀ X : Finset ℤ, X.card = 7 → (∀ F ⊆ X, F.card = 5 → ¬ Affine F) →
    ∃ x a b : ℤ, 0 < a ∧ a < b ∧ X = {x,x-a,x+a,x-b,x+b,x-(a+b),x+(a+b)}
  intro X hX hbad
  let f := X.orderEmbOfFin hX
  have mem (i : Fin 7) : f i ∈ X := X.orderEmbOfFin_mem hX i
  have hit (a b c d e : Fin 7) (ab : a < b) (bc : b < c) (cd : c < d) (de : d < e) :
      f a+f d=f b+f c ∨ f a+f e=f b+f c ∨ f a+f e=f b+f d ∨
      f a+f e=f c+f d ∨ f b+f e=f c+f d := by
    apply fiveCollision (f.strictMono ab) (f.strictMono bc) (f.strictMono cd) (f.strictMono de)
    apply hbad
    · simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem]
    · exact fiveCard (f.strictMono ab) (f.strictMono bc) (f.strictMono cd) (f.strictMono de)
  obtain ⟨sym0,sym1,sym2,rad⟩ := orderedSeven f f.strictMono hit
  have order1 := f.strictMono (show (1 : Fin 7) < 2 by decide)
  have order2 := f.strictMono (show (2 : Fin 7) < 3 by decide)
  refine ⟨f 3, f 3-f 2, f 3-f 1, by omega, by omega, ?_⟩
  have ends : X = {f 0,f 1,f 2,f 3,f 4,f 5,f 6} := by
    ext t
    constructor
    · intro ht
      obtain ⟨i,hi⟩ := (X.orderIsoOfFin hX).surjective ⟨t,ht⟩
      have he : f i = t := congrArg Subtype.val hi
      rw [← he]
      fin_cases i <;> simp
    · intro ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with h|h|h|h|h|h|h <;> rw [h] <;> exact mem _
  rw [ends, show f 3 - (f 3-f 2) = f 2 by omega,
    show f 3 + (f 3-f 2) = f 4 by omega, show f 3 - (f 3-f 1) = f 1 by omega,
    show f 3 + (f 3-f 1) = f 5 by omega, show f 3 - ((f 3-f 2)+(f 3-f 1)) = f 0 by omega,
    show f 3 + ((f 3-f 2)+(f 3-f 1)) = f 6 by omega]
  ext t
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

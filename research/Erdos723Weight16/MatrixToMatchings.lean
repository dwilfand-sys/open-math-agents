import Mathlib

/-! Necessary matching properties of the matrix in the weight-16 sparse
reduction (open-math-agents #3941 and #4185, @avivorly). -/

namespace SparseWeightSixteen
namespace Matrix

abbrev Pair := {q : Fin 8 × Fin 8 // q.1 < q.2}
abbrev Point := (Pair ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51

def pairPoint (a b : Fin 8) (h : a < b) : Point :=
  .inl (.inl ⟨(a,b),h⟩)

/-- The normalization in the upstream matrix specifies the joint occurrence
of any two distinct A-lines at a single explicitly labeled point. -/
theorem commonA_iff
    (A : Fin 8 → Point → Bool)
    (paired : ∀ a (q : Pair), A a (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2))
    (privateA : ∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b))
    (hidden : ∀ a i, A a (.inr i) = false)
    (a b : Fin 8) (h : a < b) (p : Point) :
    A a p = true ∧ A b p = true ↔ p = pairPoint a b h := by
  have ne : a ≠ b := ne_of_lt h
  cases p with
  | inl t =>
    cases t with
    | inl q =>
      simp only [paired, decide_eq_true_eq]
      constructor
      · rintro ⟨ha,hb⟩
        have e : q.val = (a,b) := by
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact (ne (ha.trans hb.symm)).elim
          · exact Prod.ext ha.symm hb.symm
          · have bad : b < a := by simpa only [ha,hb] using q.property
            exact ((not_lt_of_ge h.le) bad).elim
          · exact (ne (ha.trans hb.symm)).elim
        have eq : q = (⟨(a,b),h⟩ : Pair) := Subtype.ext e
        exact congrArg (fun t : Pair => (.inl (.inl t) : Point)) eq
      · intro e
        have eq : q = (⟨(a,b),h⟩ : Pair) := Sum.inl.inj (Sum.inl.inj e)
        rw [eq]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
    | inr t =>
      rcases t with ⟨c,i⟩
      simp only [privateA, decide_eq_true_eq]
      constructor
      · rintro ⟨ha,hb⟩
        exact (ne (ha.trans hb.symm)).elim
      · intro impossible
        cases impossible
  | inr i => simp [hidden,pairPoint]

/-- The upstream degree condition places every support point in the pair
component of the normalized point type. -/
theorem support_is_pair {A : Fin 8 → Point → Bool} (S : Finset Point)
    (privateA : ∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b))
    (hidden : ∀ a i, A a (.inr i) = false)
    (degree : ∀ p ∈ S, (Finset.univ.filter fun a => A a p = true).card = 2)
    {p : Point} (hp : p ∈ S) : ∃ q : Pair, p = .inl (.inl q) := by
  classical
  have d := degree p hp
  cases p with
  | inl r =>
    cases r with
    | inl q => exact ⟨q,rfl⟩
    | inr bi =>
      rcases bi with ⟨b,i⟩
      have points : (Finset.univ.filter fun a => A a (.inl (.inr (b,i))) = true) = {b} := by
        ext a
        simp [privateA]
      rw [points] at d
      simp at d
  | inr i => simp [hidden] at d

/-- The bit of the cubic graph means precisely that its normalized pair
point lies outside the sixteen-point support. -/
theorem graphBit_iff {A : Fin 8 → Point → Bool} (S : Finset Point)
    (a b : Fin 8) (h : a < b)
    (joint : ∀ p, A a p = true ∧ A b p = true ↔ p = pairPoint a b h) :
    (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true) ↔ pairPoint a b h ∉ S := by
  constructor
  · rintro ⟨_,p,hp,inc⟩
    simpa only [(joint p).mp inc] using hp
  · intro outside
    exact ⟨(ne_of_lt h).symm, _, outside, (joint _).mpr rfl⟩

/-- The two-secants indexed by powerset subtraction in the project are
exactly the pairs of support points sharing no four-secant. -/
theorem index_two_secant_iff {P : Type*} [DecidableEq P]
    (S : Finset P) (A : Fin 8 → P → Bool) {s t : P}
    (hs : s ∈ S) (ht : t ∈ S) (ne : s ≠ t) :
    ({s,t} : Finset P) ∈ S.powersetCard 2 \
      (Finset.univ : Finset (Fin 8)).biUnion (fun a =>
        (S.filter fun p => A a p = true).powersetCard 2) ↔
    ∀ a, ¬ (A a s = true ∧ A a t = true) := by
  classical
  have card : ({s,t} : Finset P).card = 2 := by simp [ne]
  have subset : ({s,t} : Finset P) ⊆ S := by
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  rw [Finset.mem_sdiff,Finset.mem_powersetCard]
  constructor
  · rintro ⟨_,absent⟩ a ⟨hitS,hitT⟩
    apply absent
    apply Finset.mem_biUnion.mpr
    refine ⟨a,Finset.mem_univ _,Finset.mem_powersetCard.mpr ⟨?_,card⟩⟩
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hs,hitS⟩
    · exact Finset.mem_filter.mpr ⟨ht,hitT⟩
  · intro absent
    refine ⟨⟨subset,card⟩,?_⟩
    intro common
    obtain ⟨a,_,pair⟩ := Finset.mem_biUnion.mp common
    have contained := (Finset.mem_powersetCard.mp pair).1
    exact absent a ⟨(Finset.mem_filter.mp (contained (by simp : s ∈ ({s,t} : Finset P)))).2,
      (Finset.mem_filter.mp (contained (by simp : t ∈ ({s,t} : Finset P)))).2⟩

/-- Every support point not joined to an exterior point by an A-line is
joined to it by exactly one B-line. This supplies the covering and
uniqueness properties of each matching in the finite search. -/
theorem uniqueB_of_no_commonA {I K P : Type*}
    (A : I → P → Bool) (B : K → P → Bool) (s p : P)
    (join : ∃! l : I ⊕ K, Sum.elim A B l s = true ∧ Sum.elim A B l p = true)
    (uncovered : ∀ a, ¬ (A a s = true ∧ A a p = true)) :
    ∃! b, B b s = true ∧ B b p = true := by
  obtain ⟨l,inc,uniq⟩ := join
  cases l with
  | inl a => exact (uncovered a inc).elim
  | inr b =>
    refine ⟨b,inc,?_⟩
    intro b' meet
    exact Sum.inr.inj (uniq (.inr b') meet)

/-- If an A-line already joins the two points, the matching has no B-line
there. It therefore covers exactly the residual support vertices. -/
theorem no_commonB_of_commonA {I K P : Type*}
    (A : I → P → Bool) (B : K → P → Bool) (s p : P)
    (join : ∃! l : I ⊕ K, Sum.elim A B l s = true ∧ Sum.elim A B l p = true)
    {a : I} (inc : A a s = true ∧ A a p = true) (b : K) :
    ¬ (B b s = true ∧ B b p = true) := by
  intro meet
  obtain ⟨l,_,uniq⟩ := join
  have impossible : (Sum.inl a : I ⊕ K) = .inr b :=
    (uniq (.inl a) inc).trans (uniq (.inr b) meet).symm
  cases impossible

end Matrix
end SparseWeightSixteen

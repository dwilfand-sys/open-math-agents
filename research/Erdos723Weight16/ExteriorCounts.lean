import Mathlib

/-! Exterior point counts for the exact-cover model of a sparse weight-16
configuration in a putative plane of order ten. The sets `s` below are the
chosen exterior points on a fixed line. At each point `x`, `J x` is its set
of incident A lines and `M x` its set of incident B lines. Pairwise
disjointness expresses uniqueness of each covered line-pair column. -/

namespace SparseWeightSixteen

/-- At a fixed B line, the cover forces nine exterior points. At least five
have no A incidence, so all but five of these hidden points can be dropped
when deriving a smaller necessary feasibility test. -/
theorem exteriorB_degree {P A B : Type*} [DecidableEq A] [DecidableEq B]
    (s : Finset P) (b : B) (J : P → Finset A) (M : P → Finset B)
    (through : ∀ x ∈ s, b ∈ M x)
    (localSize : ∀ x ∈ s, (M x).card + 2 * (J x).card = 8)
    (aOnce : (s : Set P).PairwiseDisjoint J)
    (bOnce : (s : Set P).PairwiseDisjoint (fun x ↦ (M x).erase b))
    (aCovered : (s.biUnion J).card = 4)
    (bCovered : (s.biUnion (fun x ↦ (M x).erase b)).card = 55) :
    s.card = 9 ∧ 5 ≤ (s.filter (fun x ↦ J x = ∅)).card := by
  have aSum := (Finset.card_biUnion aOnce).symm.trans aCovered
  have bSum := (Finset.card_biUnion bOnce).symm.trans bCovered
  have localCount (x : P) (hx : x ∈ s) : ((M x).erase b).card + 2 * (J x).card = 7 := by
    have hErase := Finset.card_erase_add_one (through x hx)
    have hLocal := localSize x hx
    omega
  have total : (∑ x ∈ s, (((M x).erase b).card + 2 * (J x).card)) = ∑ _x ∈ s, 7 :=
    Finset.sum_congr rfl localCount
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, aSum, bSum, Finset.sum_const, nsmul_eq_mul] at total
  have edgeCount := Finset.card_le_card_biUnion_add_card_fiber aOnce
  rw [aCovered] at edgeCount
  constructor <;> omega

/-- The three fixed double-A points and the A–B columns force exactly four
private exterior points on each A line. -/
theorem exteriorA_private {P B : Type*} [DecidableEq P] [DecidableEq B]
    (s d : Finset P) (M : P → Finset B)
    (hd : d ⊆ s) (three : d.card = 3)
    (once : (s : Set P).PairwiseDisjoint M) (covered : (s.biUnion M).card = 36)
    (doubleSize : ∀ x ∈ d, (M x).card = 4)
    (privateSize : ∀ x ∈ s \ d, (M x).card = 6) : (s \ d).card = 4 := by
  have tally := (Finset.card_biUnion once).symm.trans covered
  have dsum : (∑ x ∈ d, (M x).card) = ∑ _x ∈ d, 4 := Finset.sum_congr rfl doubleSize
  have ssum : (∑ x ∈ s \ d, (M x).card) = ∑ _x ∈ s \ d, 6 := Finset.sum_congr rfl privateSize
  rw [← Finset.sum_sdiff hd, dsum, ssum] at tally
  simp only [Finset.sum_const, nsmul_eq_mul, three] at tally
  omega

end SparseWeightSixteen

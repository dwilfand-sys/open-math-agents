import Mathlib

/-!
Right multiplication on a finite rational group's augmentation ideal.
This fragment follows RegularTrace.lean in the combined submission.
-/

noncomputable section

namespace MO428070

variable {G : Type*} [Group G]

def average (G : Type*) [Group G] [Fintype G] : GroupAlg G :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, MonoidAlgebra.single g (1 : ℚ)

private theorem single_times_group_sum [Fintype G] (g : G) :
    (MonoidAlgebra.single g (1 : ℚ)) * (∑ h : G, MonoidAlgebra.single h (1 : ℚ)) =
      ∑ h : G, MonoidAlgebra.single h (1 : ℚ) := by
  classical
  rw [Finset.mul_sum]
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  exact (Equiv.mulLeft g).sum_comp (fun h : G => MonoidAlgebra.single h (1 : ℚ))

theorem mul_average [Fintype G] (v : GroupAlg G) :
    v * average G = (augmentation G v) • average G := by
  let L : Module.End ℚ (GroupAlg G) := LinearMap.mulRight ℚ (average G)
  let R : Module.End ℚ (GroupAlg G) := (augmentation G).toLinearMap.smulRight (average G)
  have he : L = R := by
    apply (MonoidAlgebra.basis G ℚ).ext
    intro g
    change MonoidAlgebra.single g (1 : ℚ) * average G =
      augmentation G (MonoidAlgebra.single g (1 : ℚ)) • average G
    rw [augmentation_single, one_smul]
    unfold average
    rw [mul_smul_comm, single_times_group_sum]
  exact LinearMap.congr_fun he v

theorem aug_mul_average [Fintype G] (v : AugSpace G) : v.val * average G = 0 := by
  rw [mul_average, show augmentation G v.val = 0 from v.property, zero_smul]

def rightAug (x : GroupAlg G) : Module.End ℚ (AugSpace G) :=
  ((LinearMap.mulRight ℚ x).comp (AugSpace G).subtype).codRestrict (AugSpace G) fun v => by
    change augmentation G (v.val * x) = 0
    rw [map_mul, show augmentation G v.val = 0 from v.property, zero_mul]

@[simp] theorem rightAug_val (x : GroupAlg G) (v : AugSpace G) :
    (rightAug x v).val = v.val * x := rfl

theorem rightAug_sq [Fintype G] {x : GroupAlg G}
    (hsq : x^2 = (2:ℚ) • (1-average G)) :
    (rightAug x)^2 = (2:ℚ) • (1 : Module.End ℚ (AugSpace G)) := by
  rw [pow_two]
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (v.val*x)*x = (2:ℚ) • v.val
  rw [mul_assoc, ← pow_two, hsq, mul_smul_comm, mul_sub, mul_one, aug_mul_average, sub_zero]

theorem leftAug_commute_rightAug (g : G) (x : GroupAlg G) :
    Commute (leftAug g) (rightAug x) := by
  show leftAug g * rightAug x = rightAug x * leftAug g
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change MonoidAlgebra.single g (1:ℚ) * (v.val*x) =
    (MonoidAlgebra.single g (1:ℚ) * v.val)*x
  exact (mul_assoc _ _ _).symm

theorem average_eq_one_of_subsingleton [Fintype G] [Subsingleton G] :
    average G = 1 := by
  classical
  letI : Unique G := ⟨⟨1⟩, fun g => Subsingleton.elim g 1⟩
  simp only [average, Fintype.card_unique, Nat.cast_one, inv_one, one_smul, Fintype.sum_unique] <;> rfl

end MO428070

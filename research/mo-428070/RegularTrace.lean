import Mathlib

/-!
The rational regular representation on a finite group's augmentation ideal.
For a nonidentity translation, its trace on the whole group algebra is zero.
Projecting along the line of its multiplicative identity removes a rank-one
operator of trace one, so the trace on the augmentation ideal is minus one.
-/

noncomputable section

namespace MO428070

abbrev GroupAlg (G : Type*) [Group G] := MonoidAlgebra ℚ G

def augmentation (G : Type*) [Group G] : GroupAlg G →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ G (1 : G →* ℚ)

abbrev AugSpace (G : Type*) [Group G] : Submodule ℚ (GroupAlg G) :=
  LinearMap.ker (augmentation G).toLinearMap

variable {G : Type*} [Group G]

@[simp] theorem augmentation_single (g : G) (q : ℚ) :
    augmentation G (MonoidAlgebra.single g q) = q := by
  simp [augmentation]

def leftRegular (g : G) : Module.End ℚ (GroupAlg G) :=
  LinearMap.mulLeft ℚ (MonoidAlgebra.single g 1)

@[simp] theorem leftRegular_apply (g : G) (x : GroupAlg G) :
    leftRegular g x = MonoidAlgebra.single g 1 * x := rfl

@[simp] theorem augmentation_leftRegular (g : G) (x : GroupAlg G) :
    augmentation G (leftRegular g x) = augmentation G x := by
  rw [leftRegular_apply, map_mul, augmentation_single, one_mul]

def leftAug (g : G) : Module.End ℚ (AugSpace G) :=
  ((leftRegular g).comp (AugSpace G).subtype).codRestrict (AugSpace G) fun x => by
    change augmentation G (leftRegular g x.val) = 0
    rw [augmentation_leftRegular]
    exact x.property

@[simp] theorem leftAug_val (g : G) (x : AugSpace G) :
    (leftAug g x).val = leftRegular g x.val := rfl

def leftAugHom : G →* Module.End ℚ (AugSpace G) where
  toFun := leftAug
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (1 : GroupAlg G) * x.val = x.val
    exact one_mul _
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change MonoidAlgebra.single (g*h) (1:ℚ) * x.val =
      MonoidAlgebra.single g 1 * (MonoidAlgebra.single h 1 * x.val)
    rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

theorem leftAug_order (g : G) : leftAug g ^ orderOf g = 1 := by
  change leftAugHom g ^ orderOf g = 1
  rw [← map_pow, pow_orderOf_eq_one, map_one]

private def projectAug (G : Type*) [Group G] : GroupAlg G →ₗ[ℚ] AugSpace G :=
  (LinearMap.id - (augmentation G).toLinearMap.smulRight (1 : GroupAlg G)).codRestrict
    (AugSpace G) fun x => by
      change augmentation G (x - (augmentation G x) • (1 : GroupAlg G)) = 0
      simp

@[simp] private theorem projectAug_val (x : GroupAlg G) :
    (projectAug G x).val = x - (augmentation G x) • (1 : GroupAlg G) := rfl

theorem trace_leftRegular [Fintype G] (g : G) (hg : g ≠ 1) :
    LinearMap.trace ℚ (GroupAlg G) (leftRegular g) = 0 := by
  classical
  let b := MonoidAlgebra.basis G ℚ
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  change (∑ i, b.repr (leftRegular g (b i)) i) = 0
  apply Finset.sum_eq_zero
  intro i _
  change (MonoidAlgebra.single g (1:ℚ) * MonoidAlgebra.single i 1).coeff i = 0
  rw [MonoidAlgebra.single_mul_single, one_mul, MonoidAlgebra.coeff_single]
  apply Finsupp.single_eq_of_ne'
  intro he
  exact hg (mul_right_cancel (show g*i = 1*i by simpa only [one_mul] using he))

theorem trace_leftAug [Fintype G] (g : G) (hg : g ≠ 1) :
    LinearMap.trace ℚ (AugSpace G) (leftAug g) = -1 := by
  classical
  letI : Module.Finite ℚ (GroupAlg G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℚ)
  let P : GroupAlg G →ₗ[ℚ] AugSpace G := (projectAug G).comp (leftRegular g)
  let inc : AugSpace G →ₗ[ℚ] GroupAlg G := (AugSpace G).subtype
  have restricted : P.comp inc = leftAug g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change leftRegular g x.val - (augmentation G (leftRegular g x.val)) • (1 : GroupAlg G)
      = leftRegular g x.val
    rw [augmentation_leftRegular, show augmentation G x.val = 0 from x.property, zero_smul, sub_zero]
  have extended : inc.comp P = leftRegular g - (augmentation G).toLinearMap.smulRight (1 : GroupAlg G) := by
    apply LinearMap.ext
    intro x
    change leftRegular g x - (augmentation G (leftRegular g x)) • (1 : GroupAlg G)
      = leftRegular g x - (augmentation G x) • (1 : GroupAlg G)
    rw [augmentation_leftRegular]
  calc
    _ = LinearMap.trace ℚ (AugSpace G) (P.comp inc) := by rw [restricted]
    _ = LinearMap.trace ℚ (GroupAlg G) (inc.comp P) := LinearMap.trace_comp_comm' inc P
    _ = -1 := by
      rw [extended, map_sub, trace_leftRegular g hg, LinearMap.trace_smulRight]
      change (0:ℚ) - augmentation G 1 = -1
      rw [map_one, zero_sub]

end MO428070

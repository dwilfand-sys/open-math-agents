import OMAStatements.S_mo_428070
import Mathlib

/-!
# Square roots of two in both rational group algebras

JP McCarthy observed the augmentation obstruction for the full algebra; the
first Lean argument is adapted from Claude Code. For the augmentation ideal,
Codex uses the trace of a nonidentity translation and restriction of scalars
from the field of square root of two. The trivial group gives a zero ideal.
Source: https://mathoverflow.net/questions/428070
Credit: @dwilfand-sys, Claude Code (whole algebra) and Codex (augmentation ideal).
-/

noncomputable section

/-!
The rational regular representation on a finite group's augmentation ideal.
For a nonidentity translation, its trace on the whole group algebra is zero.
Projecting along the line of its multiplicative identity removes a rank-one
operator of trace one, so the trace on the augmentation ideal is minus one.
-/

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
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
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

/-!
Right multiplication on a finite rational group's augmentation ideal.
This fragment follows RegularTrace.lean in the combined submission.
-/

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
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => MonoidAlgebra.single h (1 : ℚ))

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

/-!
Scalar extension for the augmentation-ideal argument in MathOverflow 428070.
The quadratic algebra acts by replacing its generator with the given rational
linear operator. This construction works before a field instance is chosen.
-/

namespace MO428070.QuadraticAction

abbrev K := QuadraticAlgebra ℚ 2 0

theorem nonsquareTwoFact : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) := by
  constructor
  intro r h
  have no : ¬ IsSquare (2 : ℚ) := by norm_num
  apply no
  exact ⟨r, by simpa [pow_two] using h.symm⟩

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def representation (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V)) :
    K →ₐ[ℚ] Module.End ℚ V :=
  QuadraticAlgebra.lift ⟨T, by simpa only [pow_two, zero_smul, add_zero] using hT⟩

noncomputable abbrev scalarModule (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V)) : Module K V :=
  Module.compHom V (representation T hT).toRingHom

theorem scalar_apply (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V)) (z : K) (v : V) :
    letI := scalarModule T hT
    z • v = z.re • v + z.im • T v := by
  rfl

theorem scalarTower (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V)) :
    letI := scalarModule T hT
    IsScalarTower ℚ K V := by
  letI := scalarModule T hT
  constructor
  intro q z v
  change (q • z).re • v + (q • z).im • T v = q • (z.re • v + z.im • T v)
  simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul,
    smul_add, mul_smul]

theorem finiteOverK [Module.Finite ℚ V] (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V)) :
    letI := scalarModule T hT
    Module.Finite K V := by
  letI := scalarModule T hT
  letI := scalarTower T hT
  exact Module.Finite.of_restrictScalars_finite ℚ K V

noncomputable def liftEnd (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V))
    (L : Module.End ℚ V) (hcomm : Commute L T) :
    letI := scalarModule T hT
    Module.End K V := by
  letI := scalarModule T hT
  exact
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun z v => by
        change L (z.re • v + z.im • T v) = z.re • L v + z.im • T (L v)
        have hLT : L (T v) = T (L v) :=
          congrArg (fun f : Module.End ℚ V => f v) hcomm.eq
        simp only [map_add, map_smul, hLT] }

theorem liftEnd_apply (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V))
    (L : Module.End ℚ V) (hcomm : Commute L T) (v : V) :
    letI := scalarModule T hT
    liftEnd T hT L hcomm v = L v := by
  rfl

theorem liftEnd_restrictScalars (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V))
    (L : Module.End ℚ V) (hcomm : Commute L T) :
    letI := scalarModule T hT
    letI := scalarTower T hT
    (liftEnd T hT L hcomm).restrictScalars ℚ = L := by
  letI := scalarModule T hT
  letI := scalarTower T hT
  ext v
  rfl

theorem liftEnd_pow_apply (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V))
    (L : Module.End ℚ V) (hcomm : Commute L T) (n : ℕ) :
    letI := scalarModule T hT
    ∀ v : V, (liftEnd T hT L hcomm ^ n) v = (L ^ n) v := by
  letI := scalarModule T hT
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
    intro v
    simp only [pow_succ, Module.End.mul_apply, liftEnd_apply]
    exact ih (L v)

theorem liftEnd_pow_one (T : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V))
    (L : Module.End ℚ V) (hcomm : Commute L T) {n : ℕ} (h : L ^ n = 1) :
    letI := scalarModule T hT
    liftEnd T hT L hcomm ^ n = 1 := by
  letI := scalarModule T hT
  ext v
  exact (liftEnd_pow_apply T hT L hcomm n v).trans
    (congrArg (fun f : Module.End ℚ V => f v) h)

end MO428070.QuadraticAction

/-! Restriction of scalars and integrality of finite order traces. -/
namespace MO428070.TraceTools
open scoped BigOperators
section Restriction
variable {F K V : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V]

theorem trace_restrictScalars_of_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bK : Module.Basis ι F K) (bV : Module.Basis κ K V) (T : Module.End K V) :
    LinearMap.trace F V (T.restrictScalars F) =
      Algebra.trace F K (LinearMap.trace K V T) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace F (bK.smulTower' bV),
    LinearMap.restrictScalars_toMatrix bK bV,
    LinearMap.trace_eq_matrix_trace K bV]
  let A := LinearMap.toMatrix bV bV T
  change (∑ ij : κ × ι, (Algebra.leftMulMatrix bK (A ij.1 ij.1)) ij.2 ij.2) =
      Algebra.trace F K (∑ j : κ, A j j)
  rw [← Finset.univ_product_univ, Finset.sum_product, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (Algebra.trace_eq_matrix_trace bK (A j j)).symm

theorem trace_restrictScalars [FiniteDimensional F K] [FiniteDimensional K V]
    (T : Module.End K V) :
    LinearMap.trace F V (T.restrictScalars F) =
      Algebra.trace F K (LinearMap.trace K V T) :=
  trace_restrictScalars_of_basis (Module.Free.chooseBasis F K) (Module.Free.chooseBasis K V) T
end Restriction

section FiniteOrder
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem integral_trace_of_pow_eq_one (T : Module.End K V) {n : ℕ} (hn : 0 < n)
    (hT : T^n = 1) : IsIntegral ℤ (LinearMap.trace K V T) := by
  classical
  let E := AlgebraicClosure K
  apply (isIntegral_algebraMap_iff (R := ℤ) (A := K) (B := E)
    (algebraMap K E).injective).mp
  have hpow : (T.baseChange E)^n = 1 := by
    rw [← LinearMap.baseChange_pow, hT]
    exact LinearMap.baseChange_one _ _
  rw [← LinearMap.trace_baseChange T E,
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply IsIntegral.multiset_sum
  intro x hx
  have eigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2
    (Polynomial.isRoot_of_mem_roots hx)
  obtain ⟨v, hv⟩ := eigen.exists_hasEigenvector
  have hxpow : x^n = 1 := by
    apply smul_left_injective (R := E) hv.2
    change (x ^ n) • v = (1 : E) • v
    rw [← hv.pow_apply n, hpow]
    simp
  exact IsIntegral.of_pow hn (hxpow ▸ isIntegral_one)

end FiniteOrder
end MO428070.TraceTools

namespace MO428070.TraceObstruction

open MO428070.QuadraticAction

private theorem quadratic_trace (z : K) : Algebra.trace ℚ K z = 2 * z.re := by
  classical
  let b := QuadraticAlgebra.basis (2 : ℚ) 0
  have b0 : b 0 = (1 : K) := by
    apply b.repr.injective
    rw [Module.Basis.repr_self]
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply] <;> rfl
  have b1 : b 1 = (⟨0,1⟩ : K) := by
    apply b.repr.injective
    rw [Module.Basis.repr_self]
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace ℚ b]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, LinearMap.toMatrix_apply, b0, b1]
  change (b.repr (z * 1)) 0 + (b.repr (z * (⟨0, 1⟩ : K))) 1 = _
  simp [b, QuadraticAlgebra.im_mul, two_mul]

theorem integral_trace_ne_neg_one {z : K} (hz : IsIntegral ℤ z) :
    Algebra.trace ℚ K z ≠ -1 := by
  intro h
  rw [quadratic_trace] at h
  let q : ℚ := 2 * z.im ^ 2 - 1/4
  have ha : z.re = -(1/2 : ℚ) := by linarith
  have hq : algebraMap ℚ K q = z ^ 2 + z := by
    ext <;> simp [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, q, ha] <;> ring
  have hint : IsIntegral ℤ q := (isIntegral_algebraMap_iff
    (R := ℤ) (A := ℚ) (B := K) (algebraMap ℚ K).injective).mp (hq.symm ▸ (hz.pow 2).add hz)
  obtain ⟨N, hN⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  change (N : ℚ) = 2 * z.im ^ 2 - 1/4 at hN
  have hrat : (4 * z.im)^2 = ((8 * N + 2 : ℤ) : ℚ) := by push_cast; nlinarith
  have hi : IsIntegral ℤ (((8 * N + 2 : ℤ) : ℚ)) := isIntegral_algebraMap
  have hs : IsIntegral ℤ (4 * z.im) := IsIntegral.of_pow (n := 2) (by decide) (hrat.symm ▸ hi)
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hs
  change (y : ℚ) = 4 * z.im at hy
  rw [← hy] at hrat
  have he : y^2 = 8*N+2 := by exact_mod_cast hrat
  have hm : y^2 % 4 = 2 := by omega
  rw [pow_two, Int.mul_emod] at hm
  have cases : y%4=0 ∨ y%4=1 ∨ y%4=2 ∨ y%4=3 := by omega
  rcases cases with h0|h1|h2|h3 <;> simp_all

end MO428070.TraceObstruction

namespace MO428070

private theorem full_algebra (G : Type) [Group G] :
    ¬ ∃ x : MonoidAlgebra ℚ G, x ^ 2 = 2 := by
  rintro ⟨x, hx⟩
  obtain ⟨aug, -⟩ : ∃ aug : MonoidAlgebra ℚ G →ₐ[ℚ] ℚ, True :=
    ⟨MonoidAlgebra.lift _ _ _ (1 : G →* ℚ), trivial⟩
  have h1 : aug x ^ 2 = 2 := by
    have h := congrArg aug hx
    simpa only [map_pow, map_ofNat] using h
  have hq : Real.sqrt 2 = |((aug x : ℚ) : ℝ)| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    exact_mod_cast h1.symm
  exact irrational_sqrt_two.ne_rat |aug x| (by rw [hq, Rat.cast_abs])

private theorem trace_contradiction {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (T L : Module.End ℚ V)
    (hT : T ^ 2 = (2 : ℚ) • (1 : Module.End ℚ V)) (hc : Commute L T)
    {n : ℕ} (hn : 0 < n) (hpow : L ^ n = 1)
    (htrace : LinearMap.trace ℚ V L = -1) : False := by
  letI := QuadraticAction.nonsquareTwoFact
  letI := QuadraticAction.scalarModule T hT
  letI := QuadraticAction.scalarTower T hT
  letI := QuadraticAction.finiteOverK T hT
  let U := QuadraticAction.liftEnd T hT L hc
  have hp : U ^ n = 1 := QuadraticAction.liftEnd_pow_one T hT L hc hpow
  have hi := TraceTools.integral_trace_of_pow_eq_one U hn hp
  apply TraceObstruction.integral_trace_ne_neg_one hi
  calc
    Algebra.trace ℚ QuadraticAction.K (LinearMap.trace QuadraticAction.K V U) =
        LinearMap.trace ℚ V (U.restrictScalars ℚ) :=
      (TraceTools.trace_restrictScalars (F := ℚ) U).symm
    _ = LinearMap.trace ℚ V L := congrArg (LinearMap.trace ℚ V)
      (QuadraticAction.liftEnd_restrictScalars T hT L hc)
    _ = -1 := htrace

end MO428070

theorem OMA.solution : type_of% @OMA.S_mo_428070.main := by
  intro G hG hF
  classical
  refine ⟨MO428070.full_algebra G, ?_, ?_⟩
  · rintro ⟨x, _, hx⟩
    rcases subsingleton_or_nontrivial G with hs | hn
    · exact hs
    · letI : Nontrivial G := hn
      obtain ⟨g, hg⟩ := exists_ne (1 : G)
      letI : Module.Finite ℚ (MO428070.GroupAlg G) :=
        Module.Finite.of_basis (MonoidAlgebra.basis G ℚ)
      exact False.elim (MO428070.trace_contradiction (MO428070.rightAug x) (MO428070.leftAug g)
        (MO428070.rightAug_sq hx) (MO428070.leftAug_commute_rightAug g x)
        (orderOf_pos g) (MO428070.leftAug_order g) (MO428070.trace_leftAug g hg))
  · intro hs
    letI := hs
    refine ⟨0, map_zero _, ?_⟩
    change (0 : MO428070.GroupAlg G)^2 = (2:ℚ) • (1-MO428070.average G)
    simp [MO428070.average_eq_one_of_subsingleton]

end

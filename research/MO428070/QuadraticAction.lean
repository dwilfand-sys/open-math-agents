import Mathlib

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

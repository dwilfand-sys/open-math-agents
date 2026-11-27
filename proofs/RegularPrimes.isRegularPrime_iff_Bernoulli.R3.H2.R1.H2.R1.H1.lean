import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1
import Mathlib

/-!
# Kummer congruences for prime powers of real cyclotomic units

The project reduction is by Hanan Beer (@hananzlt), following Riccardo
Brasca and the KummerCriterion contributors. The sign identity is reused
from Hanan Beer's Apache-2.0 reduction PR 7356. The local calculation
takes the form in @Iraeeee's PR 7722: it derives Vandiver's geometric
series identity for Bernoulli-weighted moments directly.
-/

/-!
The group-theoretic index implication and real-torsion sign lemma used below
are from Hanan Beer's reduction PR 7356. Normalizing integer exponents modulo
the prime produces a relation with natural exponents in the chosen interval.
-/
namespace OMA.RealUnitRelation

open NumberField
open scoped NumberField BigOperators

lemma sign_zpow_pow {G : Type*} [CommGroup G] {ε : G}
    (hε : ε ^ 2 = 1) {p : ℕ} (hp : Odd p) (s : ℤ) :
    (ε ^ s) ^ p = ε ^ s := by
  have hsq : (ε ^ s) ^ 2 = 1 := by
    calc
      (ε ^ s) ^ 2 = (ε ^ s) ^ (2 : ℤ) := (zpow_natCast (ε ^ s) 2).symm
      _ = ε ^ (s * (2 : ℤ)) := by rw [zpow_mul]
      _ = (ε ^ (2 : ℤ)) ^ s := by rw [mul_comm, zpow_mul]
      _ = 1 := by simpa using congrArg (fun y : G => y ^ s) hε
  obtain ⟨k, hk⟩ := hp
  rw [hk, pow_add, pow_mul, hsq]
  simp

theorem normalize_full {G : Type*} [CommGroup G] {n p : ℕ} [hp : Fact p.Prime]
    (hodd : Odd p) (ε : G) (hε : ε ^ 2 = 1) (g : Fin n → G)
    (s : ℤ) (f : Fin n → ℤ) (u : G)
    (hu : u ^ p = ε ^ s * ∏ a, g a ^ f a)
    : ∃ (e : Fin n → Fin p) (w : G), (∀ a, ((e a).val : ZMod p) = (f a : ZMod p)) ∧
      w ^ p = ∏ a, g a ^ (e a).val := by
  classical
  have hpZ : 0 < (p : ℤ) := by exact_mod_cast hp.out.pos
  have hnn (a : Fin n) : 0 ≤ f a % (p : ℤ) := Int.emod_nonneg _ hpZ.ne'
  have hlt (a : Fin n) : f a % (p : ℤ) < p := Int.emod_lt_of_pos _ hpZ
  let e (a : Fin n) : Fin p :=
    ⟨(f a % (p : ℤ)).toNat, by have := hnn a; have := hlt a; omega⟩
  have remcast (a : Fin n) : ((e a).val : ℤ) = f a % (p : ℤ) :=
    Int.toNat_of_nonneg (hnn a)
  have decom (a : Fin n) : ((e a).val : ℤ) + (f a / p) * p = f a := by
    rw [remcast, mul_comm]
    exact Int.emod_add_mul_ediv _ _
  let v := ∏ a, g a ^ (f a / (p : ℤ))
  let P := ∏ a, g a ^ (e a).val
  have hf : (∏ a, g a ^ f a) = P * v ^ p := by
    dsimp only [P, v]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    calc
      g a ^ f a = g a ^ (((e a).val : ℤ) + (f a / p) * p) := congrArg _ (decom a).symm
      _ = g a ^ (e a).val * (g a ^ (f a / (p : ℤ))) ^ p := by
        simp only [zpow_add, zpow_mul, zpow_natCast]
  refine ⟨e, u / (ε ^ s * v), ?_, ?_⟩
  · intro i
    have heq := congrArg (fun t : ℤ => (t : ZMod p)) (decom i)
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      mul_zero, add_zero] at heq
    exact heq
  · change (u / (ε ^ s * v)) ^ p = P
    rw [div_pow, mul_pow, sign_zpow_pow hε hodd s, hu, hf]
    apply div_eq_iff_eq_mul.mpr
    ac_rfl

end OMA.RealUnitRelation

namespace OMA.CyclotomicResidue

open Polynomial Finset

abbrev A (p : ℕ) := AdjoinRoot ((X : (ZMod p)[X])^(p-1))

/-- Evaluation at zero factors through the truncated polynomial quotient. -/
noncomputable def atZero (p : ℕ) [Fact p.Prime] : A p →+* ZMod p :=
  AdjoinRoot.lift (f := (X : (ZMod p)[X])^(p-1)) (RingHom.id _) 0 (by
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    simp [show p-1 ≠ 0 by omega])

/-- Frobenius kills the positive-degree part of every truncated polynomial. -/
theorem pow_eq_constant {p : ℕ} [Fact p.Prime] (z : A p) :
    ∃ c : ZMod p, z^p = algebraMap (ZMod p) (A p) c := by
  let f := (X : (ZMod p)[X])^(p-1)
  obtain ⟨g, rfl⟩ := (AdjoinRoot.mk_surjective (g := f)) z
  obtain ⟨h,hh⟩ := g.X_dvd_sub_C
  have he : g = C (g.coeff 0) + X*h := by
    rw [← hh]
    ring
  have hpow : g^p = (C (g.coeff 0))^p + X^p*h^p := calc
    _ = (C (g.coeff 0)+X*h)^p := congrArg (fun t => t^p) he
    _ = _ := by rw [add_pow_char, mul_pow]
  have hz : AdjoinRoot.mk f (X^p*h^p) = 0 := by
    apply AdjoinRoot.mk_eq_zero.mpr
    exact dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.sub_le p 1)) _
  refine ⟨(g.coeff 0)^p, ?_⟩
  calc
    _ = AdjoinRoot.mk f (g^p) := (map_pow _ _ _).symm
    _ = AdjoinRoot.mk f ((C (g.coeff 0))^p) := by rw [hpow, map_add, hz, add_zero]
    _ = _ := by rw [← map_pow Polynomial.C] <;> rfl

theorem unit_pow_eq_constant {p : ℕ} [Fact p.Prime] (u : (A p)ˣ) :
    ∃ c : ZMod p, c ≠ 0 ∧ (u : A p)^p = algebraMap (ZMod p) (A p) c := by
  obtain ⟨c, hc⟩ := pow_eq_constant (u : A p)
  refine ⟨c, ?_, hc⟩
  intro hz
  have hunit : IsUnit (atZero p ((u : A p)^p)) := (u.isUnit.pow p).map (atZero p)
  apply hunit.ne_zero
  rw [hc, hz, map_zero, map_zero]

/-- Reversing the exponents in a finite geometric sum is valid even when
the ring has zero divisors. -/
theorem geom_reverse_succ {R : Type*} [CommRing R] (u : Rˣ) (n : ℕ) :
    (∑ i ∈ range (n+1), ((↑(u⁻¹) : R)^i)) =
      (↑(u⁻¹) : R)^n * ∑ i ∈ range (n+1), (u : R)^i := by
  let w : R := ↑(u⁻¹)
  have hu : w*(u : R) = 1 := u.inv_mul
  change (∑ i ∈ range (n+1), w^i) = w^n * ∑ i ∈ range (n+1), (u : R)^i
  induction n with
  | zero => simp
  | succ n ih =>
    let S : R := ∑ i ∈ range (n+1), (u : R)^i
    have hs : (∑ i ∈ range ((n+1)+1), (u : R)^i) = S*(u : R)+1 := by
      rw [Finset.sum_range_succ' (fun i => (u : R)^i) (n+1)]
      simp only [S, pow_succ, pow_zero, Finset.sum_mul]
    calc
      _ = w^n*S+w^(n+1) := by rw [Finset.sum_range_succ, ih]
      _ = w^(n+1)*(S*(u : R)+1) := by
        rw [pow_succ]
        linear_combination -(w^n*S)*hu
      _ = _ := by rw [hs]

end OMA.CyclotomicResidue

namespace OMA.CyclotomicResidue

open Polynomial NumberField

noncomputable section

/-- Reduction of the prime-index cyclotomic polynomial in characteristic p. -/
private theorem map_cyclotomic_prime (p : ℕ) [Fact p.Prime] :
    (cyclotomic p ℤ).map (Int.castRingHom (ZMod p)) = (X - 1) ^ (p - 1) := by
  rw [map_cyclotomic]
  simpa only [one_mul, cyclotomic_one] using
    cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) (p := p) (n := 1)
      (Fact.out : p.Prime).not_dvd_one

private theorem cyclotomic_at_one_add_root (p : ℕ) [Fact p.Prime] :
    aeval (1 + AdjoinRoot.root ((X : (ZMod p)[X]) ^ (p - 1)))
      (cyclotomic p ℤ) = 0 := by
  let f := (X : (ZMod p)[X]) ^ (p - 1)
  have scalar : algebraMap ℤ (A p) =
      (algebraMap (ZMod p) (A p)).comp (Int.castRingHom (ZMod p)) :=
    Subsingleton.elim _ _
  have nilpotent : (AdjoinRoot.root f) ^ (p - 1) = 0 := by
    calc
      _ = AdjoinRoot.mk f ((X : (ZMod p)[X]) ^ (p - 1)) := by
        rw [map_pow, AdjoinRoot.mk_X]
      _ = 0 := AdjoinRoot.mk_self
  rw [aeval_def, scalar, ← Polynomial.eval₂_map, map_cyclotomic_prime]
  simpa only [eval₂_pow, eval₂_sub, eval₂_X, eval₂_one, add_sub_cancel_left] using nilpotent

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

private theorem cyclotomic_integer_minpoly :
    minpoly ℤ (IsCyclotomicExtension.zeta_spec p ℚ K).integralPowerBasis.gen =
      cyclotomic p ℤ := by
  rw [IsPrimitiveRoot.integralPowerBasis_gen, ← NumberField.RingOfIntegers.minpoly_coe]
  exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
    (Fact.out : p.Prime).pos).symm

/-- The homomorphism from the ring of integers sending the canonical root to 1+T. -/
def residueHom : 𝓞 K →+* A p :=
  ((IsCyclotomicExtension.zeta_spec p ℚ K).integralPowerBasis.lift
    (1 + AdjoinRoot.root ((X : (ZMod p)[X]) ^ (p - 1))) (by
      rw [cyclotomic_integer_minpoly]
      exact cyclotomic_at_one_add_root p)).toRingHom

@[simp] theorem residueHom_zeta :
    residueHom p K (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger =
      1 + AdjoinRoot.root ((X : (ZMod p)[X]) ^ (p - 1)) := by
  rw [← IsPrimitiveRoot.integralPowerBasis_gen (IsCyclotomicExtension.zeta_spec p ℚ K)]
  unfold residueHom
  apply PowerBasis.lift_gen

end

end OMA.CyclotomicResidue

/-!
Transport the squared real cyclotomic unit relation to the ramified
residue quotient. Multiplying the image of each real generator by the
appropriate power of the root of unity clears its negative exponents.
-/
namespace OMA.CyclotomicResidue

open NumberField Polynomial
open scoped NumberField BigOperators

theorem polynomial_of_unit_relation (p : ℕ) [Fact p.Prime] :
    let K := CyclotomicField p ℚ
    let L := maximalRealSubfield K
    let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
    let z := IsCyclotomicExtension.zeta p ℚ K
    let m := (p - 3) / 2
    ∀ (g : Fin m → (𝓞 L)ˣ),
      (∀ a, algebraMap (𝓞 L) K (g a : 𝓞 L) =
        (∑ i ∈ Finset.range (a.val + 2), z ^ i) *
          (∑ i ∈ Finset.range (a.val + 2), (z⁻¹) ^ i)) →
      ∀ (e : Fin m → Fin p) (w : (𝓞 L)ˣ), w ^ p = ∏ a, g a ^ (e a).val →
      ∃ (s : ℕ) (c : ZMod p), c ≠ 0 ∧
      (X : (ZMod p)[X]) ^ (p - 1) ∣
        (∏ a : Fin m, (∑ i ∈ Finset.range (a.val + 2),
          (1 + (X : (ZMod p)[X])) ^ i) ^ (2 * (e a).val)) -
            C c * (1 + (X : (ZMod p)[X])) ^ s := by
  classical
  dsimp only
  intro g hg e w hw
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  let hz := IsCyclotomicExtension.zeta_spec p ℚ K
  let m := (p - 3) / 2
  let F := (X : (ZMod p)[X]) ^ (p - 1)
  let τ := AdjoinRoot.mk F
  let r := residueHom p K
  let φ : 𝓞 L →+* A p := r.comp (algebraMap (𝓞 L) (𝓞 K))
  let ψ : (𝓞 L)ˣ →* A p := φ.toMonoidHom.comp (Units.coeHom (𝓞 L))
  let u : (𝓞 K)ˣ := hz.unit'
  let ξ : (A p)ˣ := Units.map r.toMonoidHom u
  have hint : (u : 𝓞 K) = hz.toInteger :=
    IsUnit.unit_spec (hz.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p))
  have huz : algebraMap (𝓞 K) K (u : 𝓞 K) = z := by rw [hint]; rfl
  have huzi : algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = z⁻¹ := by
    let ρ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
    change (↑(ρ (u⁻¹)) : K) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact congrArg Inv.inv huz
  have hξ : (ξ : A p) = 1 + AdjoinRoot.root F := by
    change residueHom p K (u : 𝓞 K) = _
    rw [hint]
    exact residueHom_zeta p K
  have hX : τ (1 + (X : (ZMod p)[X])) = (ξ : A p) := by
    rw [hξ, map_add, map_one] <;> rfl
  have hC (c : ZMod p) : τ (C c) = algebraMap (ZMod p) (A p) c := rfl
  let B (a : Fin m) : A p := ∑ i ∈ Finset.range (a.val + 2), (ξ : A p)^i
  have hintegral (a : Fin m) : algebraMap (𝓞 L) (𝓞 K) (g a : 𝓞 L) =
      (∑ i ∈ Finset.range (a.val + 2), (u : 𝓞 K)^i) *
        (∑ i ∈ Finset.range (a.val + 2), (↑(u⁻¹) : 𝓞 K)^i) := by
    apply Subtype.ext
    change algebraMap (𝓞 K) K (algebraMap (𝓞 L) (𝓞 K) (g a : 𝓞 L)) =
      algebraMap (𝓞 K) K (_ * _)
    rw [← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 K) K]
    simpa only [map_mul, map_sum, map_pow, huz, huzi] using hg a
  have hlocal (a : Fin m) : ψ (g a) =
      B a * ∑ i ∈ Finset.range (a.val + 2), (↑(ξ⁻¹) : A p)^i := by
    change r (algebraMap (𝓞 L) (𝓞 K) (g a : 𝓞 L)) = _
    rw [hintegral]
    simp only [map_mul, map_sum, map_pow] <;> rfl
  have hrev (a : Fin m) : (∑ i ∈ Finset.range (a.val + 2), (↑(ξ⁻¹) : A p)^i) =
      (↑(ξ⁻¹) : A p)^(a.val + 1) * B a := geom_reverse_succ ξ (a.val + 1)
  have hcleared (a : Fin m) : ψ (g a) * (ξ : A p)^(a.val + 1) = (B a)^2 := by
    rw [hlocal, hrev]
    calc
      _ = (B a)^2 * ((↑(ξ⁻¹) : A p)^(a.val + 1) * (ξ : A p)^(a.val + 1)) := by ring
      _ = _ := by rw [← mul_pow, ξ.inv_mul, one_pow, mul_one]
  have hpow (a : Fin m) : B a ^ (2 * (e a).val) =
      ψ (g a) ^ (e a).val * (ξ : A p)^((a.val + 1) * (e a).val) := by
    rw [pow_mul, ← hcleared, mul_pow, pow_mul]
  have hrel : (ψ w)^p = ∏ a, ψ (g a)^(e a).val := by
    simpa only [map_pow, map_prod] using congrArg ψ hw
  obtain ⟨c, hc, hwc⟩ := unit_pow_eq_constant (Units.map φ.toMonoidHom w)
  have hconstant : (ψ w)^p = algebraMap (ZMod p) (A p) c := hwc
  let s := ∑ a : Fin m, (a.val + 1) * (e a).val
  have hpoly : (∏ a, B a^(2 * (e a).val)) =
      algebraMap (ZMod p) (A p) c * (ξ : A p)^s := by
    simp_rw [hpow]
    rw [Finset.prod_mul_distrib, ← hrel, hconstant, Finset.prod_pow_eq_pow_sum]
  refine ⟨s, c, hc, AdjoinRoot.mk_eq_zero.mp ?_⟩
  change τ _ = 0
  simpa only [map_sub, sub_eq_zero, map_prod, map_pow, map_sum, map_mul, hX, hC, B]
    using hpoly

end OMA.CyclotomicResidue

section

namespace OMA.RegularLocal

/-- A rational has residue `u` if it admits an integral numerator and a
denominator invertible modulo the prime. -/
def Reduces (p : ℕ) (q : ℚ) (u : ZMod p) : Prop :=
  ∃ a b : ℤ, (b : ZMod p) ≠ 0 ∧ q*(b : ℚ) = a ∧ (a : ZMod p) = u*b

namespace Reduces

theorem intCast (p : ℕ) [Fact p.Prime] (a : ℤ) :
    Reduces p (a : ℚ) (a : ZMod p) := by
  refine ⟨a, 1, ?_, ?_, ?_⟩ <;> simp

theorem zero (p : ℕ) [Fact p.Prime] : Reduces p 0 0 := by
  simpa using intCast p 0

theorem one (p : ℕ) [Fact p.Prime] : Reduces p 1 1 := by
  simpa using intCast p 1

variable {p : ℕ} [Fact p.Prime] {x y : ℚ} {u v : ZMod p}

theorem add (hx : Reduces p x u) (hy : Reduces p y v) :
    Reduces p (x+y) (u+v) := by
  obtain ⟨a,b,hb,hxa,hua⟩ := hx
  obtain ⟨c,d,hd,hyc,hvc⟩ := hy
  refine ⟨a*d+c*b, b*d, ?_, ?_, ?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hd
  · push_cast
    calc
      _ = (x*b)*d + (y*d)*b := by ring
      _ = _ := by rw [hxa, hyc]
  · push_cast
    rw [hua, hvc]
    ring

theorem neg (hx : Reduces p x u) : Reduces p (-x) (-u) := by
  obtain ⟨a,b,hb,hxa,hua⟩ := hx
  refine ⟨-a,b,hb,?_,?_⟩
  · simp only [Int.cast_neg, neg_mul, hxa]
  · simp only [Int.cast_neg, neg_mul, hua]

theorem sub (hx : Reduces p x u) (hy : Reduces p y v) :
    Reduces p (x-y) (u-v) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem mul (hx : Reduces p x u) (hy : Reduces p y v) :
    Reduces p (x*y) (u*v) := by
  obtain ⟨a,b,hb,hxa,hua⟩ := hx
  obtain ⟨c,d,hd,hyc,hvc⟩ := hy
  refine ⟨a*c,b*d,?_,?_,?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hd
  · push_cast
    calc
      _ = (x*b)*(y*d) := by ring
      _ = _ := by rw [hxa, hyc]
  · push_cast
    rw [hua, hvc]
    ring

theorem div (hx : Reduces p x u) (hy : Reduces p y v) (hv : v ≠ 0) :
    Reduces p (x/y) (u/v) := by
  obtain ⟨a,b,hb,hxa,hua⟩ := hx
  obtain ⟨c,d,hd,hyc,hvc⟩ := hy
  have hc : (c : ZMod p) ≠ 0 := hvc.symm ▸ mul_ne_zero hv hd
  have hy' : y ≠ 0 := by
    intro hz
    have hcq : (c : ℚ) = 0 := by simpa [hz] using hyc.symm
    have hci : c = 0 := by exact_mod_cast hcq
    exact hc (by simp [hci])
  refine ⟨a*d,b*c,?_,?_,?_⟩
  · simpa only [Int.cast_mul] using mul_ne_zero hb hc
  · push_cast
    calc
      _ = (x*b)*d := by rw [← hyc]; field_simp [hy'] <;> ring
      _ = _ := by rw [hxa]
  · push_cast
    rw [hua, hvc]
    field_simp [hv] <;> ring

theorem sum {ι : Type*} (s : Finset ι) (x : ι → ℚ) (u : ι → ZMod p)
    (h : ∀ i ∈ s, Reduces p (x i) (u i)) :
    Reduces p (∑ i ∈ s, x i) (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero p
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem unique (hx : Reduces p x u) (hy : Reduces p x v) : u = v := by
  obtain ⟨a,b,hb,hxa,hua⟩ := hx
  obtain ⟨c,d,hd,hxc,hvc⟩ := hy
  have he : a*d = c*b := by
    have hq : (a : ℚ)*d = (c : ℚ)*b := by rw [← hxa, ← hxc]; ring
    exact_mod_cast hq
  have hcross := congrArg (fun z : ℤ => (z : ZMod p)) he
  change ((a*d : ℤ) : ZMod p) = ((c*b : ℤ) : ZMod p) at hcross
  simp only [Int.cast_mul, hua, hvc] at hcross
  have hzero : (u-v)*((b : ZMod p)*d) = 0 := by linear_combination hcross
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (mul_ne_zero hb hd))

/-- Clear the denominator of the original rational even when its canonical
denominator is divisible by the reduction prime. -/
theorem num_mul_eq_zero {r : ℚ} {v : ℤ} (h : Reduces p (r*(v : ℚ)) 0) :
    (r.num : ZMod p)*(v : ZMod p) = 0 := by
  obtain ⟨a,b,hb,hq,ha⟩ := h
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hr : (r.num : ℚ) = r*(r.den : ℚ) := (div_eq_iff hden).mp r.num_div_den
  have he : (r.num*v)*b = a*(r.den : ℤ) := by
    have hrat : ((r.num : ℚ)*v)*b = (a : ℚ)*r.den := by
      rw [hr, ← hq]
      ring
    exact_mod_cast hrat
  have hcross := congrArg (fun z : ℤ => (z : ZMod p)) he
  change (((r.num*v)*b : ℤ) : ZMod p) = ((a*(r.den : ℤ) : ℤ) : ZMod p) at hcross
  have ha0 : (a : ZMod p) = 0 := by simpa using ha
  simp only [Int.cast_mul, ha0, zero_mul] at hcross
  exact (mul_eq_zero.mp hcross).resolve_right hb

end Reduces
end OMA.RegularLocal

end

section

open Polynomial

namespace RegularExponentialMoments

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def eulerOp (U : R[X]) : R[X] := (1 + X) * U.derivative

/-- The value at zero of the `k`-fold application of `(1+X) d/dX`. -/
def moment : ℕ → R[X] → R
  | 0, U => U.eval 0
  | k + 1, U => moment k (eulerOp U)

theorem eulerOp_map (f : R →+* S) (U : R[X]) :
    eulerOp (U.map f) = (eulerOp U).map f := by
  simp [eulerOp, Polynomial.derivative_map]

theorem moment_map (f : R →+* S) (k : ℕ) (U : R[X]) :
    moment k (U.map f) = f (moment k U) := by
  induction k generalizing U with
  | zero => simp [moment]
  | succ k ih => rw [moment, moment, eulerOp_map, ih]

theorem moment_sub (k : ℕ) (U V : R[X]) :
    moment k (U - V) = moment k U - moment k V := by
  induction k generalizing U V with
  | zero => simp [moment]
  | succ k ih =>
    change moment k (eulerOp (U - V)) = moment k (eulerOp U) - moment k (eulerOp V)
    rw [← ih]
    simp [eulerOp, Polynomial.derivative_sub, mul_sub]

theorem moment_zero_of_X_pow_dvd {n k : ℕ} {U : R[X]}
    (hn : k < n) (hU : (X : R[X]) ^ n ∣ U) : moment k U = 0 := by
  induction k generalizing n U with
  | zero =>
    exact (Polynomial.coeff_zero_eq_eval_zero U).symm.trans
      ((Polynomial.X_pow_dvd_iff.mp hU) 0 hn)
  | succ k ih =>
    apply ih (n := n - 1) (by omega)
    exact dvd_mul_of_dvd_right (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hU) _

private theorem eulerOp_shift (s : ℕ) (c : R) :
    eulerOp (C c * (1 + X) ^ s) = C (c * (s : R)) * (1 + X) ^ s := by
  cases s with
  | zero => simp [eulerOp]
  | succ s =>
    unfold eulerOp
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow_succ]
    simp only [Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_add,
      Polynomial.derivative_one, Polynomial.derivative_X, mul_one, Nat.cast_succ,
      map_mul, pow_succ]
    ring

theorem moment_shift (k s : ℕ) (c : R) :
    moment k (C c * (1 + X) ^ s) = c * (s : R) ^ k := by
  induction k generalizing c with
  | zero => simp [moment]
  | succ k ih =>
    rw [moment, eulerOp_shift, ih, pow_succ]
    ring

/-- The modulus may be composite. This assertion uses only a congruence in `(ZMod p)[X]`. -/
theorem moment_congr_shift {p s k : ℕ} (U : ℤ[X]) (c : ZMod p)
    (h : (X : (ZMod p)[X]) ^ (p - 1) ∣ U.map (Int.castRingHom (ZMod p)) - C c * (1 + X) ^ s)
    (hk : k < p - 1) : (moment k U : ZMod p) = c * (s : ZMod p) ^ k := by
  have h0 := moment_zero_of_X_pow_dvd hk h
  rw [moment_sub, moment_map, moment_shift, sub_eq_zero] at h0
  exact h0

/-- Substitution of `exp(t)-1` into an integral polynomial. -/
def exponentialSeries (U : ℤ[X]) : PowerSeries ℚ :=
  Polynomial.aeval (PowerSeries.exp ℚ - 1) (U.map (Int.castRingHom ℚ))

theorem exponentialSeries_eq_eval₂ (U : ℤ[X]) :
    exponentialSeries U = U.eval₂ (PowerSeries.C.comp (Int.castRingHom ℚ))
      (PowerSeries.exp ℚ - 1) := by
  rw [exponentialSeries, Polynomial.aeval_def, Polynomial.eval₂_map]
  exact Polynomial.eval₂_congr (Subsingleton.elim _ _) rfl rfl

theorem constantCoeff_exponentialSeries (U : ℤ[X]) :
    PowerSeries.constantCoeff (exponentialSeries U) = (moment 0 U : ℚ) := by
  rw [exponentialSeries_eq_eval₂, Polynomial.hom_eval₂]
  simp [moment, ← Polynomial.coeff_zero_eq_eval_zero]

theorem derivative_exponentialSeries (U : ℤ[X]) :
    PowerSeries.derivative ℚ (exponentialSeries U) = exponentialSeries (eulerOp U) := by
  unfold exponentialSeries
  rw [Derivation.comp_aeval_eq, ← eulerOp_map]
  simp [eulerOp, smul_eq_mul, PowerSeries.derivative_exp, PowerSeries.derivative_one]
  <;> ring

/-- The factorial clears all denominators in each exponential coefficient. -/
theorem moment_eq_factorial_coeff (k : ℕ) (U : ℤ[X]) :
    (moment k U : ℚ) = (k.factorial : ℚ) * PowerSeries.coeff k (exponentialSeries U) := by
  rw [← PowerSeries.constantCoeff_iterate_derivative]
  induction k generalizing U with
  | zero => exact (constantCoeff_exponentialSeries U).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply, derivative_exponentialSeries]
    exact ih (eulerOp U)

end

end RegularExponentialMoments

end

section

namespace OMA.RegularLocal

open Finset PowerSeries

noncomputable section

/-- The geometric cyclotomic unit after substituting the formal exponential. -/
def geomSeries (a : ℕ) : PowerSeries ℚ :=
  ∑ i ∈ range a, exp ℚ ^ i

/-- The scaled Bernoulli series minus its unscaled value. -/
def bernWeight (a : ℕ) : PowerSeries ℚ :=
  rescale (a : ℚ) (bernoulli'PowerSeries ℚ) - bernoulli'PowerSeries ℚ

/-- A denominator-free logarithmic-derivative identity. Multiplying by
`exp(X) − 1` reduces each side to the two Bernoulli generating identities. -/
theorem geom_differential (a : ℕ) :
    X * (d⁄dX ℚ (geomSeries a)) = geomSeries a * bernWeight a := by
  let E := exp ℚ
  let B := bernoulli'PowerSeries ℚ
  let G := geomSeries a
  have e0 : E-1 ≠ 0 := by
    intro he
    have h := congrArg (coeff 1) he
    norm_num [E] at h
  have bg : B * (E-1) = X*E := bernoulli'PowerSeries_mul_exp_sub_one ℚ
  have ba : rescale (a:ℚ) B * (E^a-1) = (a:PowerSeries ℚ)*X*E^a := by
    have h := congrArg (rescale (a:ℚ)) bg
    simpa only [E, exp_pow_eq_rescale_exp, map_mul, map_sub, map_one,
      rescale_X, map_natCast] using h
  have identity : (E-1)*G=E^a-1 := mul_geom_sum E a
  have diffPow : d⁄dX ℚ (E^a) = (a:PowerSeries ℚ)*E^a := by
    rw [PowerSeries.derivative_pow, show d⁄dX ℚ E = E from derivative_exp ℚ]
    cases a with
    | zero => simp
    | succ a => simp only [Nat.succ_sub_one, pow_succ]; ring
  have differentiated := congrArg (derivative ℚ) identity
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, sub_zero,
    show d⁄dX ℚ E = E from derivative_exp ℚ, diffPow, smul_eq_mul] at differentiated
  change X*(d⁄dX ℚ G) = G*(rescale (a:ℚ) B-B)
  apply mul_left_cancel₀ e0
  calc
    (E-1)*(X*(d⁄dX ℚ G)) = X*((a:PowerSeries ℚ)*E^a-G*E) := by
      linear_combination X*differentiated
    _ = rescale (a:ℚ) B*(E^a-1)-B*(E-1)*G := by rw [ba,bg]; ring
    _ = (E-1)*(G*(rescale (a:ℚ) B-B)) := by rw [← identity]; ring

private theorem combine {F G H K : PowerSeries ℚ}
    (hf : X*(d⁄dX ℚ F)=F*H) (hg : X*(d⁄dX ℚ G)=G*K) :
    X*(d⁄dX ℚ (F*G))=(F*G)*(H+K) := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  linear_combination G*hf + F*hg

private theorem repeated {F H : PowerSeries ℚ}
    (hf : X*(d⁄dX ℚ F)=F*H) (k : ℕ) :
    X*(d⁄dX ℚ (F^k))=F^k*(C (k:ℚ)*H) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simpa only [pow_succ, Nat.cast_succ, map_add, map_one, add_mul, one_mul]
      using combine ih hf

theorem product_differential {ι : Type*} (s : Finset ι) (a e : ι → ℕ) :
    X*(d⁄dX ℚ (∏ i ∈ s, geomSeries (a i)^(e i))) =
      (∏ i ∈ s, geomSeries (a i)^(e i)) *
        (∑ i ∈ s, C (e i:ℚ)*bernWeight (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [prod_insert hi,sum_insert hi]
    exact combine (repeated (geom_differential (a i)) (e i)) ih

theorem bernoulli_weighted_coeff {ι : Type*} (s : Finset ι) (a e : ι → ℕ) (n : ℕ) :
    (n.factorial:ℚ) * coeff n (∑ i ∈ s, C (e i:ℚ)*bernWeight (a i)) =
      bernoulli' n * ∑ i ∈ s, (e i:ℚ)*((a i:ℚ)^n-1) := by
  have hn : (n.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [map_sum, mul_sum, mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [bernWeight, coeff_C_mul, map_sub, coeff_rescale, bernoulli'PowerSeries,
    coeff_mk, Algebra.algebraMap_self_apply]
  field_simp [hn]
  <;> ring

end

end OMA.RegularLocal

end

section

namespace OMA.RegularLocal

open Finset Finset.Nat PowerSeries

theorem factorial_residue_ne {p k : ℕ} [Fact p.Prime] (hk : k<p) :
    (k.factorial : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  exact (not_le_of_gt hk) (hp.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff ..).mp h))

private theorem natRed (p k : ℕ) [Fact p.Prime] : Reduces p (k:ℚ) (k:ZMod p) := by
  simpa only [Int.cast_natCast] using Reduces.intCast p (k:ℤ)

/-- A series with invertible leading coefficient cancels from a finite
string of coefficients reducing to zero, even if the coefficients being
solved for are initially arbitrary rationals. -/
private theorem cancel_coeffs {p N : ℕ} [Fact p.Prime] (U L : PowerSeries ℚ)
    (v : ℕ → ZMod p) (h0 : v 0 ≠ 0)
    (hU : ∀ j<N, Reduces p (coeff j U) (v j))
    (hP : ∀ j<N, Reduces p (coeff j (L*U)) 0) :
    ∀ j<N, Reduces p (coeff j L) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have du := hU 0 (by omega)
    have hnz : coeff 0 U ≠ 0 := by
      intro hz
      rw [hz] at du
      exact h0 (du.unique (Reduces.zero p))
    let f (i j : ℕ) := coeff i L * coeff j U
    have low : Reduces p (∑ i ∈ range n, f i (n-i)) 0 := by
      have h := Reduces.sum (range n) (fun i => f i (n-i)) (fun _ => (0:ZMod p))
        (fun i hi => by
          have hil := mem_range.mp hi
          simpa only [f,zero_mul] using (ih i hil (by omega)).mul (hU (n-i) (by omega)))
      simpa only [sum_const_zero] using h
    have expansion : coeff n (L*U) = (∑ i ∈ range n, f i (n-i)) + coeff n L * coeff 0 U := by
      rw [coeff_mul]
      change (∑ t ∈ antidiagonal n, f t.1 t.2) = _
      rw [sum_antidiagonal_eq_sum_range_succ f, sum_range_succ, Nat.sub_self]
    have hp := (hP n hn).sub low
    rw [expansion, add_sub_cancel_left] at hp
    have hr := hp.div du h0
    simpa [hnz] using hr

/-- If U agrees to order N with a nonzero multiple of exp(sX) modulo p,
XU'/U has vanishing coefficients in degrees 2 through N−1. -/
theorem local_differential_vanish {p N s : ℕ} [Fact p.Prime] (hNp : N≤p)
    {c : ZMod p} (hc : c≠0) (U B : PowerSeries ℚ)
    (hU : ∀ k<N, Reduces p (coeff k U) (c*(s:ZMod p)^k/(k.factorial:ZMod p)))
    (hIdentity : X*(d⁄dX ℚ U)=U*B)
    {k : ℕ} (hk : 2≤k) (hN : k<N) : Reduces p (coeff k B) 0 := by
  let L := B-C (s:ℚ)*X
  have eqn : L*U = X*(d⁄dX ℚ U)-C (s:ℚ)*(X*U) := by
    dsimp only [L]
    rw [hIdentity]
    ring
  have hP (j : ℕ) (hj : j<N) : Reduces p (coeff j (L*U)) 0 := by
    rw [eqn, map_sub, coeff_C_mul]
    cases j with
    | zero => simpa only [coeff_zero_X_mul, mul_zero, sub_zero] using Reduces.zero p
    | succ r =>
      rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative]
      have ht := ((hU (r+1) hj).mul (natRed p (r+1))).sub ((natRed p s).mul (hU r (by omega)))
      have hfac := factorial_residue_ne (p:=p) (k:=r) (by omega)
      have hsucc : ((r+1:ℕ):ZMod p) ≠ 0 := by
        intro h
        have hd := (ZMod.natCast_eq_zero_iff _ _).mp h
        have hi := Nat.le_of_dvd (show 0<r+1 by omega) hd
        omega
      have hz : c*(s:ZMod p)^(r+1)/((r+1).factorial:ZMod p)*((r+1:ℕ):ZMod p) -
          (s:ZMod p)*(c*(s:ZMod p)^r/(r.factorial:ZMod p)) = 0 := by
        rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
        field_simp [hfac, hsucc]
        <;> ring
      rw [hz] at ht
      simpa only [Nat.cast_add, Nat.cast_one] using ht
  have hzero : c*(s:ZMod p)^0/(Nat.factorial 0:ZMod p)≠0 := by simpa using hc
  have hL := cancel_coeffs U L _ hzero hU hP k hN
  have hne : k≠1 := by omega
  simpa only [L,map_sub,coeff_C_mul,coeff_X,if_neg hne,mul_zero,sub_zero] using hL

end OMA.RegularLocal

end

section

namespace OMA.RegularLocal

open Finset Polynomial RegularExponentialMoments

noncomputable section

theorem local_geometric_moments (p : ℕ) [Fact p.Prime] :
    let m := (p-3)/2
    ∀ (e : Fin m → Fin p) (s : ℕ) (c : ZMod p), c ≠ 0 →
      (Polynomial.X : (ZMod p)[X])^(p-1) ∣
        (∏ i : Fin m, (∑ t ∈ range (i.val+2), (1+(Polynomial.X : (ZMod p)[X]))^t)^(2*(e i).val)) -
          Polynomial.C c * (1+Polynomial.X)^s →
      ∀ j : Fin m, ((bernoulli (2*(j.val+1))).num : ZMod p) *
        (∑ i, ((e i).val : ZMod p)*(((((i.val+2:ℕ):ZMod p)^2)^(j.val+1))-1)) = 0 := by
  classical
  let m := (p-3)/2
  dsimp only
  intro e s c hc hrel j
  let a (i : Fin m) := i.val+2
  let E (i : Fin m) := 2*(e i).val
  let n := 2*(j.val+1)
  have hj := j.isLt
  change j.val < (p-3)/2 at hj
  have hn : 2≤n := by dsimp [n]; omega
  have hnp : n<p-1 := by dsimp [n]; omega
  have hp5 : 5≤p := by omega
  let P : ℤ[X] := ∏ i : Fin m, (∑ t ∈ range (a i), (1+(Polynomial.X : ℤ[X]))^t)^(E i)
  have hpoly : (Polynomial.X : (ZMod p)[X])^(p-1) ∣
      P.map (Int.castRingHom (ZMod p))-Polynomial.C c*(1+Polynomial.X)^s := by
    simpa only [P,a,E,Polynomial.map_prod,Polynomial.map_pow,Polynomial.map_sum,
      Polynomial.map_add,Polynomial.map_one,Polynomial.map_X] using hrel
  let U := ∏ i : Fin m, geomSeries (a i)^(E i)
  let B := ∑ i : Fin m, PowerSeries.C (E i:ℚ)*bernWeight (a i)
  have fromPoly : exponentialSeries P = U := by
    have he : 1+(PowerSeries.exp ℚ-1)=PowerSeries.exp ℚ := by ring
    simp [exponentialSeries,P,U,geomSeries,Polynomial.map_prod,Polynomial.map_sum,he]
  have coeffs (k : ℕ) (hk : k<p-1) : Reduces p (PowerSeries.coeff k U)
      (c*(s:ZMod p)^k/(k.factorial:ZMod p)) := by
    have h := Reduces.intCast p (moment k P)
    rw [moment_congr_shift P c hpoly hk] at h
    have hf := natRed p k.factorial
    have d := h.div hf (factorial_residue_ne (by omega : k<p))
    have hq : (moment k P : ℚ)/(k.factorial:ℚ) = PowerSeries.coeff k U := by
      rw [moment_eq_factorial_coeff, fromPoly]
      have hnonzero : (k.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      field_simp
    rwa [hq] at d
  have diff : PowerSeries.X*(PowerSeries.derivative ℚ U)=U*B :=
    product_differential univ a E
  have h0 := local_differential_vanish (N:=p-1) (by omega) hc U B coeffs diff hn hnp
  have scaled := (natRed p n.factorial).mul h0
  have hcoeff := bernoulli_weighted_coeff univ a E n
  change (n.factorial:ℚ)*PowerSeries.coeff n B =
    bernoulli' n * ∑ i : Fin m, (E i:ℚ)*((a i:ℚ)^n-1) at hcoeff
  have hBern : bernoulli' n = bernoulli n := by
    rw [bernoulli'_eq_bernoulli, Even.neg_one_pow (even_two_mul (j.val+1)), one_mul]
  let v : ℤ := ∑ i : Fin m, (E i:ℤ)*((a i:ℤ)^n-1)
  have vQ : (v:ℚ) = ∑ i : Fin m, (E i:ℚ)*((a i:ℚ)^n-1) := by
    simp [v]
  rw [hcoeff, hBern, ← vQ, mul_zero] at scaled
  have z := Reduces.num_mul_eq_zero scaled
  let w := ∑ i : Fin m, ((e i).val : ZMod p)*(((((i.val+2:ℕ):ZMod p)^2)^(j.val+1))-1)
  have vF : (v:ZMod p) = 2*w := by
    dsimp only [v,w]
    simp only [Int.cast_sum,Int.cast_mul,Int.cast_sub,Int.cast_one,Int.cast_pow,Int.cast_natCast]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp only [a,E,n]
    push_cast
    rw [← pow_mul]
    ring
  rw [vF] at z
  have h2 : (2:ZMod p) ≠ 0 := by
    intro hh
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hh)
    have := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  change ((bernoulli n).num:ZMod p)*w=0
  apply (mul_eq_zero.mp (show (2:ZMod p)*(((bernoulli n).num:ZMod p)*w)=0 by
    linear_combination z)).resolve_left h2

end
end OMA.RegularLocal

end

open scoped NumberField BigOperators
open NumberField

/-!
With the cyclotomic variables reduced modulo p, the local Bernoulli identity
is insensitive to the multiples of p removed from the integer exponents.
-/
theorem OMA.solution :
    OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1.H1 := by
  intro p hp hp5
  dsimp only
  intro g hg s f u hu j
  have hodd := hp.out.odd_of_ne_two (show p ≠ 2 by omega)
  obtain ⟨e, w, hres, hw⟩ := OMA.RealUnitRelation.normalize_full hodd
    (-1 : (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))ˣ) (by ext; simp) g s f u hu
  obtain ⟨t, c, hc, hpoly⟩ := OMA.CyclotomicResidue.polynomial_of_unit_relation p g hg e w hw
  have hm := OMA.RegularLocal.local_geometric_moments p e t c hc hpoly j
  have hs : (∑ a, ((e a).val : ZMod p) * (((((a.val + 2 : ℕ) : ZMod p)^2)^(j.val + 1)) - 1)) =
      ∑ a, (((a.val + 2 : ℕ) : ZMod p)^(2 * (j.val + 1)) - 1) * (f a : ZMod p) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hres a, ← pow_mul]
    exact mul_comm _ _
  rwa [hs] at hm

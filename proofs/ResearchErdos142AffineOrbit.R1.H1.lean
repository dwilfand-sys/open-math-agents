import OMAReductions.R_ResearchErdos142AffineOrbit_R1
import Mathlib

/-! Codex for dwilfand-sys. Solve the unit-factor equation in the quotient,
then lift its positive representative and translate one endpoint. -/
namespace AffineOrbit
open OMA.R_ResearchErdos142AffineOrbit_R1

theorem transitive : H1 := by
  intro p e h a b hp hpos ha hb x y z w first second
  letI : NeZero (p^h) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨A,hA⟩ := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hpos).2 ha
  obtain ⟨B,hB⟩ := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hpos).2 hb
  let V := B*A⁻¹
  let u := (V : ZMod (p^h)).val
  have castU : (u : ZMod (p^h))=(V : ZMod (p^h)) := ZMod.natCast_zmod_val _
  have un : IsUnit (u : ZMod (p^h)) := castU ▸ V.isUnit
  have nod : ¬p∣u := (ZMod.isUnit_natCast_iff_not_dvd_pow hp hpos).1 un
  have cu : u.Coprime (p^(e+h)) :=
    ((ZMod.isUnit_iff_coprime u (p^(e+h))).1
      ((ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0<e+h by omega)).2 nod))
  have sm : ((u*a : ℕ) : ZMod (p^h))=(b : ZMod (p^h)) := by
    rw [Nat.cast_mul,castU,←hA,←hB]
    simp [V,mul_assoc]
  have modEq := (ZMod.natCast_eq_natCast_iff _ _ _).mp sm
  have scaled : p^e*(u*a) ≡ p^e*b [MOD p^(e+h)] := by
    rw [pow_add]
    exact modEq.mul_left' (p^e)
  have big := (ZMod.natCast_eq_natCast_iff _ _ _).2 scaled
  have line : (u : ZMod (p^(e+h)))*(y-x)=w-z := by
    rw [first,second]
    push_cast at big ⊢
    linear_combination big
  refine ⟨u,ZMod.val_lt _,cu,z-u*x,by ring,?_⟩
  linear_combination line

end AffineOrbit

theorem OMA.solution : OMA.R_ResearchErdos142AffineOrbit_R1.H1 := AffineOrbit.transitive

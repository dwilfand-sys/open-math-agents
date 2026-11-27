import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1
import Mathlib

/-!
# Bernoulli moments of truncated geometric products

This proves the local finite-field step posed in @Iraeeee's reduction #7722.
The geometric-factor identity is the formal logarithmic-derivative
calculation used by Vandiver. We use its denominator-free form throughout.
The rational reduction relation permits cancellation of a unit leading
coefficient without any separate Bernoulli-denominator theorem.
-/

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

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2_H2_R1.H2 := by
  intro p h
  exact OMA.RegularLocal.local_geometric_moments p

end

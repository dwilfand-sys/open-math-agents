import OMAReductions.R_oeis_a056828_R1
import Mathlib

/-!
# Exceptional squarefree kernels in Mollin and Walsh's conjecture

For each e ∈ {7,15,23,87,111,119} and prime p > 31, the ternary quadratic
form x² + 8s² + 27z² represents e p². Its nonzero terms are powerful.

Write p as a sum of four squares and interpret these four coordinates as an
integer quaternion q. Conjugating a pure quaternion of squared length 6e
by q gives three integer coordinates of squared length 6e p². The first
finite calculation finds a permutation and signs that place those coordinates
in the sublattice corresponding to x² + 8s² + 27z². After allowing one
reflection, every surviving quaternion is projectively congruent to a vector
on one of five explicit lines.

At each such line three integral normals have squared length six. Reflection
in any of their perpendicular hyperplanes preserves the norm and fixes the
line. Distinct possible lines are separated modulo 3 or 9. The three normals
therefore force the same congruence to lift through every power of 3. Bounding
the finitely many integer minors turns congruence into exact collinearity.
The five line generators have squared lengths 1, 2, 4, 5, and 11, which
excludes prime norms above 31.
-/

/-!
Hamilton conjugation and the lattice for the ternary form x² + 8s² + 27z².
The congruence test may permute and sign the coordinates of the rotated vector.
Only equality of the two squared lengths is needed below.
-/

namespace MollinWalshPrime

abbrev V4 := Fin 4 → ℤ
abbrev V3 := Fin 3 → ℤ

def norm4 (q : V4) : ℤ := ∑ i, (q i)^2
def norm3 (v : V3) : ℤ := ∑ i, (v i)^2

theorem norm4_coords (q : V4) : norm4 q = (q 0)^2+(q 1)^2+(q 2)^2+(q 3)^2 := by
  simp [norm4, Fin.sum_univ_succ, add_assoc]

theorem norm3_coords (v : V3) : norm3 v = (v 0)^2+(v 1)^2+(v 2)^2 := by
  simp [norm3, Fin.sum_univ_succ, add_assoc]

/-- The imaginary coordinates of q w q̄, for purely imaginary w. -/
def rotate (q : V4) (w : V3) : V3 :=
  let a := q 0
  let i := q 1
  let j := q 2
  let k := q 3
  let x := w 0
  let y := w 1
  let z := w 2
  let h := a^2-i^2-j^2-k^2
  let t := i*x+j*y+k*z
  ![h*x+2*i*t+2*a*(j*z-k*y),
    h*y+2*j*t+2*a*(k*x-i*z),
    h*z+2*k*t+2*a*(i*y-j*x)]

private theorem hamiltonIdentity (a i j k x y z : ℤ) :
    let h := a^2-i^2-j^2-k^2
    let t := i*x+j*y+k*z
    (h*x+2*i*t+2*a*(j*z-k*y))^2 + (h*y+2*j*t+2*a*(k*x-i*z))^2 +
      (h*z+2*k*t+2*a*(i*y-j*x))^2 = (a^2+i^2+j^2+k^2)^2 * (x^2+y^2+z^2) := by
  dsimp
  ring

theorem norm3_rotate (q : V4) (w : V3) :
    norm3 (rotate q w) = (norm4 q)^2 * norm3 w := by
  rw [norm3_coords, norm4_coords, norm3_coords]
  exact hamiltonIdentity (q 0) (q 1) (q 2) (q 3) (w 0) (w 1) (w 2)

theorem exists_norm4_nat (p : ℕ) : ∃ q : V4, norm4 q = (p : ℤ) := by
  obtain ⟨a,b,c,d,h⟩ := Nat.sum_four_squares p
  refine ⟨![(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ)], ?_⟩
  rw [norm4_coords]
  change (a : ℤ)^2+(b : ℤ)^2+(c : ℤ)^2+(d : ℤ)^2 = (p : ℤ)
  exact_mod_cast h

/-- Integral points of the indicated sublattice recover x, s and z. -/
theorem represent_of_triple {n : ℤ} (v : V3) (hn : norm3 v = 6*n)
    (h18 : (18 : ℤ) ∣ v 0 + v 1) (h12 : (12 : ℤ) ∣ v 0 - v 1 + v 2)
    (h6 : (6 : ℤ) ∣ v 0 - v 1 - 2*v 2) :
    ∃ x s z : ℤ, n = x^2+8*s^2+27*z^2 := by
  obtain ⟨x,hx⟩ := h6
  obtain ⟨s,hs⟩ := h12
  obtain ⟨z,hz⟩ := h18
  have hb : v 0 = x+4*s+9*z := by omega
  have hc : v 1 = -x-4*s+9*z := by omega
  have hd : v 2 = -2*x+4*s := by omega
  have hsum : norm3 v = 6*(x^2+8*s^2+27*z^2) := by
    rw [norm3_coords,hb,hc,hd]
    ring
  exact ⟨x,s,z,mul_left_cancel₀ (by decide : (6 : ℤ) ≠ 0) (hn.symm.trans hsum)⟩

theorem represent_of_rotation {p m : ℤ} (q : V4) (w v : V3)
    (hq : norm4 q = p) (hw : norm3 w = 6*m) (hv : norm3 v = norm3 (rotate q w))
    (h18 : (18 : ℤ) ∣ v 0 + v 1) (h12 : (12 : ℤ) ∣ v 0 - v 1 + v 2)
    (h6 : (6 : ℤ) ∣ v 0 - v 1 - 2*v 2) :
    ∃ x s z : ℤ, p^2*m = x^2+8*s^2+27*z^2 := by
  refine represent_of_triple v ?_ h18 h12 h6
  rw [hv,norm3_rotate,hq,hw]
  ring

private theorem powerfulSquareCube (a b : ℕ) :
    a^2*b^3 = 0 ∨ OMA.S_oeis_a056828.IsPowerful (a^2*b^3) := by
  by_cases ha : a = 0
  · exact Or.inl (by simp [ha])
  by_cases hb : b = 0
  · exact Or.inl (by simp [hb])
  refine Or.inr ⟨Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero ha) _) (pow_pos (Nat.pos_of_ne_zero hb) _), ?_⟩
  intro q hq hd
  rcases hq.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hq.dvd_of_dvd_pow h) 2) _
  · have hb2 : q^2 ∣ b^2 := pow_dvd_pow_of_dvd (hq.dvd_of_dvd_pow h) 2
    exact dvd_mul_of_dvd_right (hb2.trans (pow_dvd_pow b (by decide : 2 ≤ 3))) _

theorem powerful_of_ternary {n : ℕ} {x s z : ℤ} (hn : (n : ℤ) = x^2+8*s^2+27*z^2) :
    ∃ a b c : ℕ, (a = 0 ∨ OMA.S_oeis_a056828.IsPowerful a) ∧
      (b = 0 ∨ OMA.S_oeis_a056828.IsPowerful b) ∧
      (c = 0 ∨ OMA.S_oeis_a056828.IsPowerful c) ∧ a+b+c = n := by
  refine ⟨x.natAbs^2, s.natAbs^2*2^3, z.natAbs^2*3^3, ?_,
    powerfulSquareCube _ _, powerfulSquareCube _ _, ?_⟩
  · simpa using powerfulSquareCube x.natAbs 1
  · apply Int.ofNat.inj
    push_cast
    try simp only [Int.natCast_natAbs, sq_abs]
    rw [hn] <;> ring

end MollinWalshPrime

namespace MollinWalshPrime

-- Compiled after the definitions of V4 and norm4 from MWHamilton.
def SignedPerm (x y : V4) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∃ ε : Fin 4 → Bool,
    ∀ i, y i = if ε i then -x (σ i) else x (σ i)

def axisL : V4 := ![0,0,0,1]
def fourL : V4 := ![1,1,1,1]
def fiveL : V4 := ![0,0,1,2]
def twoL : V4 := ![0,0,1,1]
def elevenL : V4 := ![0,1,1,3]

def lineSeeds (m : ℕ) (splitCase : Bool) : List V4 :=
  if splitCase then (if m=23 then [axisL, fourL] else [axisL])
  else if m=7 then [fiveL] else if m=23 then [twoL, elevenL] else []

def allowedLine (m : ℕ) (splitCase : Bool) (L : V4) : Prop :=
  ∃ W ∈ lineSeeds m splitCase, SignedPerm W L

def Near (q L : V4) (N : ℕ) : Prop :=
  ∀ i j, (N : ℤ) ∣ q i * L j - q j * L i

def nearBase (p : ℕ) : ℕ := if p%3=1 then 9 else 27

def transverse (u L : V4) : Prop := ∃ i j, ¬ (3 : ℤ) ∣ u i*L j-u j*L i

def lineNormals (L : V4) : V4 → V4 → V4 → Prop := fun u v w =>
  norm4 u=6 ∧ norm4 v=6 ∧ norm4 w=6 ∧
  (∑ i, u i*L i)=0 ∧ (∑ i, v i*L i)=0 ∧ (∑ i, w i*L i)=0 ∧
  transverse u L ∧ transverse v L ∧ transverse w L ∧
  ∀ s : V4, (3:ℤ) ∣ (∑ i, u i*s i) → (3:ℤ) ∣ (∑ i, v i*s i) →
    (3:ℤ) ∣ (∑ i, w i*s i) → Near s L 3

end MollinWalshPrime

namespace MWExactLine

abbrev V := Fin 4 → ℤ

def minor (q L : V) (i j : Fin 4) : ℤ := q i * L j - q j * L i

def Near (q L : V) (N : ℕ) : Prop := ∀ i j, (N : ℤ) ∣ minor q L i j

def norm (q : V) : ℤ := ∑ i, q i ^ 2

theorem near_of_scalar_residue {q L : V} {N : ℕ} {a : ℤ}
    (h : ∀ i, (N : ℤ) ∣ q i - a * L i) : Near q L N := by
  intro i j
  obtain ⟨u, hu⟩ := h i
  obtain ⟨v, hv⟩ := h j
  refine ⟨u * L j - v * L i, ?_⟩
  unfold minor
  linear_combination L j * hu - L i * hv

theorem scalar_residue_of_near {q L : V} {N : ℕ} (h : Near q L N)
    (hpivot : ∃ j, L j = 1 ∨ L j = -1) :
    ∃ a : ℤ, ∀ i, (N : ℤ) ∣ q i - a * L i := by
  obtain ⟨j, hj | hj⟩ := hpivot
  · exact ⟨q j, fun i => by simpa [minor, hj] using h i j⟩
  · refine ⟨-q j, ?_⟩
    intro i
    obtain ⟨w, hw⟩ := h i j
    unfold minor at hw
    rw [hj] at hw
    refine ⟨-w, ?_⟩
    linear_combination -hw

private theorem lt_three_pow (k : ℕ) : k < 3 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    omega

private theorem eq_zero_of_large_dvd {x : ℤ} {N : ℕ}
    (hd : (N : ℤ) ∣ x) (hb : x.natAbs < N) : x = 0 := by
  by_contra hx
  have hpos : 0 < x.natAbs := Int.natAbs_pos.mpr hx
  obtain ⟨y, hy⟩ := hd
  have hd' : N ∣ x.natAbs := ⟨y.natAbs, by rw [hy, Int.natAbs_mul, Int.natAbs_natCast]⟩
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hd')) hb

theorem zero_minors_of_near_every_power {q L : V}
    (h : ∀ k : ℕ, 3 ≤ k → Near q L (3 ^ k)) : ∀ i j, minor q L i j = 0 := by
  intro i j
  let B := (minor q L i j).natAbs
  apply eq_zero_of_large_dvd (h (B+3) (by omega) i j)
  exact lt_trans (show B < B+3 by omega) (lt_three_pow (B+3))

/-- The sum of the absolute minors simultaneously bounds all minors of all candidate lines. -/
theorem exact_line_in_family {q : V} {F : Finset V}
    (h : ∀ k : ℕ, 3 ≤ k → ∃ L ∈ F, Near q L (3 ^ k)) :
    ∃ L ∈ F, ∀ i j, minor q L i j = 0 := by
  classical
  let B : ℕ := ∑ L ∈ F, ∑ i : Fin 4, ∑ j : Fin 4, (minor q L i j).natAbs
  obtain ⟨L, hL, hnear⟩ := h (B+3) (by omega)
  refine ⟨L, hL, ?_⟩
  intro i j
  have hbound : (minor q L i j).natAbs ≤ B := by
    calc
      _ ≤ ∑ b : Fin 4, (minor q L i b).natAbs :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ ∑ a : Fin 4, ∑ b : Fin 4, (minor q L a b).natAbs :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ ≤ B := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hL
  exact eq_zero_of_large_dvd (hnear i j)
    (lt_of_le_of_lt hbound (lt_trans (show B < B+3 by omega) (lt_three_pow (B+3))))

theorem one_line_near_every_power {q : V} {F : Finset V}
    (h : ∀ k : ℕ, 3 ≤ k → ∃ L ∈ F, Near q L (3 ^ k)) :
    ∃ L ∈ F, ∀ k : ℕ, Near q L (3 ^ k) := by
  obtain ⟨L, hL, hz⟩ := exact_line_in_family h
  refine ⟨L, hL, ?_⟩
  intro k i j
  rw [hz i j]
  exact dvd_zero _

theorem multiple_of_zero_minors {q L : V} (h : ∀ i j, minor q L i j = 0)
    (hpivot : ∃ j, L j = 1 ∨ L j = -1) : ∃ c : ℤ, ∀ i, q i = c * L i := by
  obtain ⟨j, hj | hj⟩ := hpivot
  · refine ⟨q j, ?_⟩
    intro i
    have e : q i * L j - q j * L i = 0 := h i j
    rw [hj] at e
    linear_combination e
  · refine ⟨-q j, ?_⟩
    intro i
    have e : q i * L j - q j * L i = 0 := h i j
    rw [hj] at e
    linear_combination -e

theorem multiple_of_near_every_power {q L : V}
    (h : ∀ k : ℕ, 3 ≤ k → Near q L (3 ^ k))
    (hpivot : ∃ j, L j = 1 ∨ L j = -1) : ∃ c : ℤ, ∀ i, q i = c * L i :=
  multiple_of_zero_minors (zero_minors_of_near_every_power h) hpivot

theorem prime_norm_excludes_multiple {p : ℕ} (hp : p.Prime) {q L : V}
    (hq : norm q = (p : ℤ)) (hL : (norm L).natAbs < p)
    (hm : ∃ c : ℤ, ∀ i, q i = c * L i) : False := by
  obtain ⟨c, hc⟩ := hm
  have hnorm : norm q = c ^ 2 * norm L := by
    unfold norm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc i]
    ring
  rw [hq] at hnorm
  have he : p = c.natAbs ^ 2 * (norm L).natAbs := by
    simpa only [pow_two, Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hnorm
  have hd : (norm L).natAbs ∣ p := ⟨c.natAbs ^ 2, by rw [he, Nat.mul_comm]⟩
  have hone : (norm L).natAbs = 1 := ((Nat.dvd_prime hp).mp hd).resolve_right (Nat.ne_of_lt hL)
  rw [hone, Nat.mul_one] at he
  exact (Nat.prime_iff.mp hp).not_isSquare ⟨c.natAbs, by simpa only [pow_two] using he⟩

theorem impossible_exceptional_norm_line {p : ℕ} (hp : p.Prime) (hbig : 31 < p) {q L : V}
    (hq : norm q = (p : ℤ)) (hL : norm L ∈ ({1, 2, 4, 5, 11} : Finset ℤ))
    (hpivot : ∃ j, L j = 1 ∨ L j = -1) (h : ∀ i j, minor q L i j = 0) : False := by
  have hb : (norm L).natAbs < p := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with hL | hL | hL | hL | hL <;> rw [hL] <;> norm_num <;> omega
  exact prime_norm_excludes_multiple hp hq hb (multiple_of_zero_minors h hpivot)

theorem impossible_exceptional_family {p : ℕ} (hp : p.Prime) (hbig : 31 < p) {q : V}
    (hq : norm q = (p : ℤ)) {F : Finset V}
    (hL : ∀ L ∈ F, norm L ∈ ({1, 2, 4, 5, 11} : Finset ℤ))
    (hpiv : ∀ L ∈ F, ∃ j, L j = 1 ∨ L j = -1)
    (h : ∀ k : ℕ, 3 ≤ k → ∃ L ∈ F, Near q L (3 ^ k)) : False := by
  obtain ⟨L, hmem, hz⟩ := exact_line_in_family h
  exact impossible_exceptional_norm_line hp hbig hq (hL L hmem) (hpiv L hmem) hz

end MWExactLine

namespace MollinWalshPrime

theorem signed_trans {x y z : V4} (hxy : SignedPerm x y) (hyz : SignedPerm y z) :
    SignedPerm x z := by
  obtain ⟨σ, ε, h₁⟩ := hxy
  obtain ⟨τ, δ, h₂⟩ := hyz
  refine ⟨τ.trans σ, fun i => Bool.xor (δ i) (ε (τ i)), ?_⟩
  intro i
  cases hd : δ i <;> cases he : ε (τ i) <;> simp [h₂, h₁, hd, he]

theorem pull_near_signed {m N : ℕ} {splitCase : Bool} {x y L : V4} (h : SignedPerm x y)
    (ha : allowedLine m splitCase L) (hn : Near y L N) :
    ∃ M, allowedLine m splitCase M ∧ Near x M N := by
  obtain ⟨σ, ε, hq⟩ := h
  let M : V4 := fun i => if ε (σ.symm i) then -L (σ.symm i) else L (σ.symm i)
  obtain ⟨W, hW, hWL⟩ := ha
  have hLM : SignedPerm L M := ⟨σ.symm, fun i => ε (σ.symm i), fun _ => rfl⟩
  refine ⟨M, ⟨W, hW, signed_trans hWL hLM⟩, ?_⟩
  intro i j
  obtain ⟨k,hk⟩ := hn (σ.symm i) (σ.symm j)
  have hi : y (σ.symm i) = (if ε (σ.symm i) then -x i else x i) := by
    simpa using hq (σ.symm i)
  have hj : y (σ.symm j) = (if ε (σ.symm j) then -x j else x j) := by
    simpa using hq (σ.symm j)
  rw [hi,hj] at hk
  cases he : ε (σ.symm i) <;> cases hf : ε (σ.symm j) <;> simp [M, he, hf] at hk ⊢
  all_goals first
    | exact ⟨k, by linear_combination hk⟩
    | exact ⟨-k, by linear_combination -hk⟩

def dot4 (q v : V4) : ℤ := ∑ i, q i*v i

theorem reflection_norm (q v : V4) (k : ℤ) (hv : norm4 v=6) (hd : dot4 q v=3*k) :
    norm4 (fun i => q i-k*v i)=norm4 q := by
  have e : norm4 (fun i => q i-k*v i) = norm4 q-2*k*dot4 q v+k^2*norm4 v := by
    simp only [norm4, dot4, Fin.sum_univ_four]
    ring
  rw [e, hv, hd]
  ring

private lemma cancel_unit {R : ℕ} (hR : R=3 ∨ R=9) (a z : ℤ)
    (ha : ¬(3 : ℤ) ∣ a) (h : (R : ℤ) ∣ a*z) : (R : ℤ) ∣ z := by
  have prim : Prime (3 : ℤ) := by norm_num
  rcases hR with rfl | rfl
  · exact (prim.dvd_mul.mp h).resolve_left ha
  · have h3 : (3 : ℤ) ∣ a*z := (show (3 : ℤ) ∣ 9 by decide).trans h
    obtain ⟨b, hb⟩ := (prim.dvd_mul.mp h3).resolve_left ha
    obtain ⟨v, hv⟩ := h
    have h3' : (3 : ℤ) ∣ a*b := ⟨v, by rw [hb] at hv; nlinarith only [hv]⟩
    obtain ⟨w, hw⟩ := (prim.dvd_mul.mp h3').resolve_left ha
    exact ⟨w, by rw [hb,hw]; ring⟩

/-- Increase the congruence modulus by three. After each orthogonal reflection
the usual separation of projective directions returns the same rational line. -/
theorem lift_step {p D R : ℕ} {F : V4 → Prop}
    (hD : 0 < D) (hR : R=3 ∨ R=9) (hdvd : R ∣ D) (hp3 : ¬(3 : ℤ) ∣ (p : ℤ))
    (pivot : ∀ L, F L → ∃ i, L i=1 ∨ L i= -1)
    (normals : ∀ L, F L → ∃ u v w, lineNormals L u v w)
    (sep : ∀ L K, F L → F K → Near L K R → K=L ∨ K=fun i => -L i)
    (old : ∀ q, norm4 q=(p : ℤ) → ∃ L, F L ∧ Near q L (3*D)) :
    ∀ q, norm4 q=(p : ℤ) → ∃ L, F L ∧ Near q L (3*(3*D)) := by
  classical
  intro q hn
  obtain ⟨L, hL, near⟩ := old q hn
  obtain ⟨a, ha⟩ := MWExactLine.scalar_residue_of_near
    (q := q) (L := L) (N := 3*D) near (pivot L hL)
  choose s hs using ha
  have coord (i : Fin 4) : q i=a*L i+3*(D : ℤ)*s i := by
    have e := hs i
    push_cast at e
    linear_combination e
  have unit : ¬(3 : ℤ) ∣ a := by
    rintro ⟨b, hb⟩
    have hc (i : Fin 4) : (3 : ℤ) ∣ q i := ⟨b*L i+D*s i, by rw [coord, hb]; ring⟩
    have hsum : (3 : ℤ) ∣ norm4 q := by
      change (3 : ℤ) ∣ ∑ i, (q i)^2
      apply Finset.dvd_sum
      intro i _
      simpa only [pow_two] using dvd_mul_of_dvd_left (hc i) (q i)
    exact hp3 (hn ▸ hsum)
  obtain ⟨u,v,w, nu,nv,nw, ou,ov,ow, tu,tv,tw, basis⟩ := normals L hL
  have each (z : V4) (nz : norm4 z=6) (oz : dot4 z L=0) (tz : transverse z L) :
      (3 : ℤ) ∣ dot4 z s := by
    let f := dot4 z s
    let δ : ℤ := D
    let Q : V4 := fun i => q i - δ*f*z i
    have eqdot : dot4 q z=3*(δ*f) := by
      simp only [f, δ, dot4, Fin.sum_univ_four, coord] at oz ⊢
      linear_combination a * oz
    have hnQ : norm4 Q=(p : ℤ) := (reflection_norm q z (δ*f) nz eqdot).trans hn
    obtain ⟨K,hK,hQ⟩ := old Q hnQ
    have qc (i : Fin 4) : Q i=a*L i+δ*(3*s i-f*z i) := by
      dsimp only [Q,δ]
      rw [coord]
      ring
    have close : Near L K R := by
      intro i j
      apply cancel_unit hR a _ unit
      obtain ⟨c,hc⟩ := hQ i j
      have cast : ((3*D : ℕ) : ℤ)=3*δ := by dsimp only [δ]; norm_cast
      rw [cast, qc, qc] at hc
      obtain ⟨g,hg⟩ := hdvd
      have hδ : δ=(R : ℤ)*(g : ℤ) := by dsimp only [δ]; exact_mod_cast hg
      refine ⟨(g : ℤ)*(3*c-(3*s i-f*z i)*K j+(3*s j-f*z j)*K i), ?_⟩
      rw [hδ] at hc
      linear_combination hc
    have same : Near Q L (3*D) := by
      rcases sep L K hL hK close with h | h
      · simpa only [h] using hQ
      · intro i j
        obtain ⟨c,hc⟩ := hQ i j
        rw [h] at hc
        exact ⟨-c, by linear_combination -hc⟩
    obtain ⟨i,j,ht⟩ := tz
    obtain ⟨c,hc⟩ := same i j
    have cast : ((3*D : ℕ) : ℤ)=3*δ := by dsimp only [δ]; norm_cast
    rw [cast, qc, qc] at hc
    have nonzero : δ ≠ 0 := by dsimp only [δ]; exact_mod_cast (Nat.ne_of_gt hD)
    have hprod : δ * (f*(z i*L j-z j*L i))=δ*(3*(s i*L j-s j*L i-c)) := by
      linear_combination -hc
    have hd : (3 : ℤ) ∣ f*(z i*L j-z j*L i) := ⟨_, mul_left_cancel₀ nonzero hprod⟩
    have prim : Prime (3 : ℤ) := by norm_num
    exact (prim.dvd_mul.mp hd).resolve_right ht
  have hsmall := basis s (each u nu ou tu) (each v nv ov tv) (each w nw ow tw)
  refine ⟨L,hL,?_⟩
  intro i j
  obtain ⟨b,hb⟩ := hsmall i j
  refine ⟨b,?_⟩
  push_cast
  rw [coord, coord]
  linear_combination (3*(D : ℤ))*hb

theorem iterated_lift {p R : ℕ} {F : V4 → Prop} (hR : R=3 ∨ R=9)
    (hp3 : ¬(3 : ℤ) ∣ (p : ℤ))
    (pivot : ∀ L, F L → ∃ i, L i=1 ∨ L i= -1)
    (normals : ∀ L, F L → ∃ u v w, lineNormals L u v w)
    (sep : ∀ L K, F L → F K → Near L K R → K=L ∨ K=fun i => -L i)
    (base : ∀ q, norm4 q=(p : ℤ) → ∃ L, F L ∧ Near q L (3*R)) :
    ∀ q, norm4 q=(p : ℤ) → ∀ k : ℕ, ∃ L, F L ∧ Near q L (3^k) := by
  have all (j : ℕ) : ∀ q, norm4 q=(p : ℤ) → ∃ L, F L ∧ Near q L (3*(R*3^j)) := by
    induction j with
    | zero => simpa using base
    | succ j ih =>
      have hpos : 0<R := by omega
      have hd : R ∣ R*3^j := ⟨_,rfl⟩
      have h := lift_step (D := R*3^j) (by positivity) hR hd hp3 pivot normals sep ih
      have hre : 3*(R*3^(j+1))=3*(3*(R*3^j)) := by rw [pow_succ]; ring
      rw [hre]
      exact h
  intro q hq k
  obtain ⟨L,hL,hnear⟩ := all k q hq
  refine ⟨L,hL,fun i j => ?_⟩
  have div : ((3^k : ℕ) : ℤ) ∣ ((3*(R*3^k) : ℕ) : ℤ) := ⟨3*(R : ℤ),by push_cast; ring⟩
  exact div.trans (hnear i j)

end MollinWalshPrime

namespace MollinWalshPrime

private def geomSign (b : Bool) : ℤ := if b then -1 else 1

private def geomAct (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) (x : V4) : V4 :=
  fun i => geomSign (ε i) * x (σ i)

private def geomModel : Fin 5 → V4 := ![axisL, fourL, fiveL, twoL, elevenL]

private def geomU : Fin 5 → V4 :=
  ![![2,1,1,0], ![-2,1,1,0], ![1,0,2,-1], ![0,2,1,-1], ![2,1,-1,0]]
private def geomV : Fin 5 → V4 :=
  ![![2,1,-1,0], ![-2,1,0,1], ![-1,0,2,-1], ![0,-2,1,-1], ![-2,1,-1,0]]
private def geomW : Fin 5 → V4 :=
  ![![2,-1,1,0], ![-2,0,1,1], ![0,1,2,-1], ![2,0,1,-1], ![0,2,1,-1]]

private theorem geomModelIndex {m : ℕ} {s : Bool} {L : V4} (h : L ∈ lineSeeds m s) :
    ∃ k : Fin 5, L = geomModel k ∧ (k.val < 2 ↔ s = true) := by
  cases s
  · by_cases h7 : m = 7
    · simp [lineSeeds,h7] at h
      exact ⟨2, h, by decide⟩
    · by_cases h23 : m = 23
      · simp [lineSeeds,h7,h23] at h
        rcases h with h | h
        · exact ⟨3, h, by decide⟩
        · exact ⟨4, h, by decide⟩
      · simp [lineSeeds,h7,h23] at h
  · by_cases h23 : m = 23
    · simp [lineSeeds,h23] at h
      rcases h with h | h
      · exact ⟨0, h, by decide⟩
      · exact ⟨1, h, by decide⟩
    · simp [lineSeeds,h23] at h
      exact ⟨0, h, by decide⟩

private theorem geomRepresentation {m : ℕ} {s : Bool} {L : V4} (h : allowedLine m s L) :
    ∃ (k : Fin 5) (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool),
      (k.val < 2 ↔ s = true) ∧ L = geomAct σ ε (geomModel k) := by
  obtain ⟨W,hW,σ,ε,he⟩ := h
  obtain ⟨k,rfl,hk⟩ := geomModelIndex hW
  refine ⟨k,σ,ε,hk,?_⟩
  funext i
  cases hε : ε i <;> simpa [geomAct,geomSign,hε] using he i

private theorem geomActInverse (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) (x : V4) :
    geomAct σ.symm (fun j => ε (σ.symm j)) (geomAct σ ε x) = x := by
  funext i
  cases h : ε (σ.symm i) <;> simp [geomAct,geomSign,h]

private theorem geomActInverse' (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) (x : V4) :
    geomAct σ ε (geomAct σ.symm (fun j => ε (σ.symm j)) x) = x := by
  funext i
  cases h : ε i <;> simp [geomAct,geomSign,h]

private theorem geomDotAct (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) (u v : V4) :
    (∑ i, geomAct σ ε u i * geomAct σ ε v i) = ∑ i, u i * v i := by
  calc
    _ = ∑ i, u (σ i) * v (σ i) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : ε i <;> simp [geomAct,geomSign,h]
    _ = _ := Equiv.sum_comp σ (fun i => u i * v i)

private theorem geomNormAct (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool) (u : V4) :
    norm4 (geomAct σ ε u) = norm4 u := by
  simpa only [norm4,pow_two] using geomDotAct σ ε u u

private theorem geomNearAct {q L : V4} {N : ℕ} (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool)
    (h : Near q L N) : Near (geomAct σ ε q) (geomAct σ ε L) N := by
  intro i j
  obtain ⟨c,hc⟩ := h (σ i) (σ j)
  refine ⟨geomSign (ε i) * geomSign (ε j) * c, ?_⟩
  unfold geomAct
  linear_combination (geomSign (ε i) * geomSign (ε j)) * hc

private theorem geomTransverseAct {q L : V4} (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool)
    (h : transverse q L) : transverse (geomAct σ ε q) (geomAct σ ε L) := by
  classical
  by_contra hno
  have hall : Near (geomAct σ ε q) (geomAct σ ε L) 3 := by
    intro i j
    by_contra hn
    exact hno ⟨i,j,hn⟩
  have hback := geomNearAct σ.symm (fun j => ε (σ.symm j)) hall
  rw [geomActInverse,geomActInverse] at hback
  obtain ⟨i,j,hn⟩ := h
  exact hn (hback i j)

private theorem geomNormalAct {L u v w : V4} (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → Bool)
    (h : lineNormals L u v w) :
    lineNormals (geomAct σ ε L) (geomAct σ ε u) (geomAct σ ε v) (geomAct σ ε w) := by
  obtain ⟨nu,nv,nw,ou,ov,ow,tu,tv,tw,span⟩ := h
  refine ⟨(geomNormAct σ ε u).trans nu, (geomNormAct σ ε v).trans nv,
    (geomNormAct σ ε w).trans nw, (geomDotAct σ ε u L).trans ou,
    (geomDotAct σ ε v L).trans ov, (geomDotAct σ ε w L).trans ow,
    geomTransverseAct σ ε tu, geomTransverseAct σ ε tv, geomTransverseAct σ ε tw, ?_⟩
  intro z hu hv hw
  let f := geomAct σ.symm (fun j => ε (σ.symm j)) z
  have hf : geomAct σ ε f = z := geomActInverse' σ ε z
  have back (a : V4) (hz : (3 : ℤ) ∣ ∑ i, geomAct σ ε a i * z i) :
      (3 : ℤ) ∣ ∑ i, a i * f i := by
    rwa [← geomDotAct σ ε a f,hf]
  have hh := geomNearAct σ ε (span f (back u hu) (back v hv) (back w hw))
  rwa [hf] at hh

private def geomDotMod (u : V4) (z : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ i, (u i : ZMod 3) * z i

private theorem geomDotModZero {u s : V4} (h : (3 : ℤ) ∣ ∑ i, u i * s i) :
    geomDotMod u (fun i => (s i : ZMod 3)) = 0 := by
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ i, u i * s i) 3).mpr h
  simpa only [geomDotMod,Int.cast_sum,Int.cast_mul] using hc

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem geomSpanCertificate :
    ∀ (k : Fin 5) (z : Fin 4 → ZMod 3),
        geomDotMod (geomU k) z = 0 → geomDotMod (geomV k) z = 0 →
        geomDotMod (geomW k) z = 0 → ∀ i j,
        z i * (geomModel k j : ZMod 3) - z j * (geomModel k i : ZMod 3) = 0 := by
  decide +kernel

private theorem geomModelNormals (k : Fin 5) :
    lineNormals (geomModel k) (geomU k) (geomV k) (geomW k) := by
  have finiteFacts : ∀ t : Fin 5, norm4 (geomU t) = 6 ∧ norm4 (geomV t) = 6 ∧
      norm4 (geomW t) = 6 ∧ (∑ i, geomU t i * geomModel t i) = 0 ∧
      (∑ i, geomV t i * geomModel t i) = 0 ∧ (∑ i, geomW t i * geomModel t i) = 0 ∧
      (∃ i j, ¬ (3 : ℤ) ∣ geomU t i * geomModel t j - geomU t j * geomModel t i) ∧
      (∃ i j, ¬ (3 : ℤ) ∣ geomV t i * geomModel t j - geomV t j * geomModel t i) ∧
      (∃ i j, ¬ (3 : ℤ) ∣ geomW t i * geomModel t j - geomW t j * geomModel t i) := by
    decide +kernel
  obtain ⟨a,b,c,d,e,f,g,h,j⟩ := finiteFacts k
  refine ⟨a,b,c,d,e,f,g,h,j,?_⟩
  intro z hu hv hw i j
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  push_cast
  exact geomSpanCertificate k (fun t => (z t : ZMod 3))
    (geomDotModZero hu) (geomDotModZero hv) (geomDotModZero hw) i j

theorem allowedLine_normals {m : ℕ} {s : Bool} {L : V4} (h : allowedLine m s L) :
    ∃ u v w, lineNormals L u v w := by
  obtain ⟨k,σ,ε,_,rfl⟩ := geomRepresentation h
  exact ⟨_,_,_,geomNormalAct σ ε (geomModelNormals k)⟩

theorem allowedLine_pivot {m : ℕ} {s : Bool} {L : V4} (h : allowedLine m s L) :
    ∃ j, L j = 1 ∨ L j = -1 := by
  obtain ⟨k,σ,ε,_,rfl⟩ := geomRepresentation h
  have pivots : ∀ t : Fin 5, ∃ i, geomModel t i = 1 := by decide
  obtain ⟨i,hi⟩ := pivots k
  refine ⟨σ.symm i, ?_⟩
  cases hε : ε (σ.symm i) <;> simp [geomAct,geomSign,hε,hi]

theorem allowedLine_norm {m : ℕ} {s : Bool} {L : V4} (h : allowedLine m s L) :
    norm4 L ∈ ({1,2,4,5,11} : Finset ℤ) := by
  obtain ⟨k,σ,ε,_,rfl⟩ := geomRepresentation h
  rw [geomNormAct]
  exact (by decide : ∀ t : Fin 5, norm4 (geomModel t) ∈ ({1,2,4,5,11} : Finset ℤ)) k

theorem allowedLine_finset (m : ℕ) (s : Bool) :
    ∃ F : Finset V4, ∀ L, L ∈ F ↔ allowedLine m s L := by
  classical
  let I := Fin 5 × Equiv.Perm (Fin 4) × (Fin 4 → Bool)
  let T : I → V4 := fun t => geomAct t.2.1 t.2.2 (geomModel t.1)
  refine ⟨(Finset.univ.image T).filter (allowedLine m s), ?_⟩
  intro L
  rw [Finset.mem_filter]
  refine ⟨And.right, ?_⟩
  intro h
  obtain ⟨k,σ,ε,_,hL⟩ := geomRepresentation h
  exact ⟨Finset.mem_image.mpr ⟨(k,σ,ε),Finset.mem_univ _,hL.symm⟩,h⟩

private def geomBound (b x : ℤ) : Prop := -b ≤ x ∧ x ≤ b

private theorem geomBounds :
    ∀ (k : Fin 5) (i : Fin 4) (e : Bool), let x := geomSign e * geomModel k i
      geomBound 3 x ∧ (k.val < 2 → geomBound 1 x) ∧
      (k.val = 2 → geomBound 2 x) ∧ (k.val ≠ 2 → x ≠ 2 ∧ x ≠ -2) := by
  decide +kernel

/-- For a unit coordinate multiplier the congruences here already give an integer equality.
When the multiplier is 2 or -2, its own line is a signed permutation of the norm-five line. -/
private theorem geomSmallGap (s : Bool) (x y c : ℤ)
    (hx : geomBound 3 x) (hy : geomBound 3 y) (hc : geomBound 3 c)
    (hs : s = true → geomBound 1 x ∧ geomBound 1 y ∧ geomBound 1 c)
    (hshape : (geomBound 2 y ∧ geomBound 2 c) ∨ (c ≠ 2 ∧ c ≠ -2))
    (hu : ¬ (3 : ℤ) ∣ c) (hd : ((if s then 3 else 9 : ℕ) : ℤ) ∣ y - c*x) :
    y = c*x := by
  unfold geomBound at *
  obtain ⟨c₀,c₁⟩ := hc
  cases s
  · change (9 : ℤ) ∣ y-c*x at hd
    rcases hshape with h | h <;> interval_cases c <;> omega
  · have h := hs rfl
    change (3 : ℤ) ∣ y-c*x at hd
    interval_cases c <;> omega

theorem allowedLine_separated {m : ℕ} {s : Bool} {L K : V4}
    (hL : allowedLine m s L) (hK : allowedLine m s K)
    (hn : Near L K (if s then 3 else 9)) :
    K = L ∨ K = fun i => -L i := by
  obtain ⟨j,hj⟩ := allowedLine_pivot hL
  obtain ⟨r,hr⟩ := allowedLine_pivot hK
  obtain ⟨k,σ,ε,hk,eL⟩ := geomRepresentation hL
  obtain ⟨t,τ,δ,ht,eK⟩ := geomRepresentation hK
  let c := K j * L j
  have hj2 : L j ^ 2 = 1 := by rcases hj with h | h <;> rw [h] <;> norm_num
  have hres (i : Fin 4) : ((if s then 3 else 9 : ℕ) : ℤ) ∣ K i - c * L i := by
    obtain ⟨v,hv⟩ := hn i j
    refine ⟨-L j * v, ?_⟩
    dsimp [c]
    linear_combination -(L j) * hv - (K i) * hj2
  have hu : ¬ (3 : ℤ) ∣ c := by
    intro hc
    have h3 : (3 : ℤ) ∣ ((if s then 3 else 9 : ℕ) : ℤ) := by cases s <;> decide
    obtain ⟨v,hv⟩ := h3.trans (hres r)
    obtain ⟨w,hw⟩ := hc
    have hd : (3 : ℤ) ∣ K r := ⟨v+w*L r, by linear_combination hv + L r * hw⟩
    rcases hr with h | h <;> rw [h] at hd <;> norm_num at hd
  obtain ⟨e,he⟩ : ∃ e : Bool, c = geomSign e * geomModel t (τ j) := by
    rcases hj with h | h
    · refine ⟨δ j, ?_⟩
      dsimp [c]
      rw [h,mul_one]
      exact congrFun eK j
    · refine ⟨!(δ j), ?_⟩
      dsimp [c]
      rw [h,eK]
      cases hb : δ j <;> simp [geomAct,geomSign,hb]
  have all (i : Fin 4) : K i = c * L i := by
    have bx := geomBounds k (σ i) (ε i)
    have by' := geomBounds t (τ i) (δ i)
    have bc := geomBounds t (τ j) e
    have ex : L i = geomSign (ε i) * geomModel k (σ i) := congrFun eL i
    have ey : K i = geomSign (δ i) * geomModel t (τ i) := congrFun eK i
    rw [← ex] at bx
    rw [← ey] at by'
    rw [← he] at bc
    apply geomSmallGap s _ _ _ bx.1 by'.1 bc.1 _ _ hu (hres i)
    · intro hs
      exact ⟨bx.2.1 (hk.mpr hs), by'.2.1 (ht.mpr hs), bc.2.1 (ht.mpr hs)⟩
    · by_cases htwo : t.val = 2
      · exact Or.inl ⟨by'.2.2.1 htwo,bc.2.2.1 htwo⟩
      · exact Or.inr (bc.2.2.2 htwo)
  have hc : c = 1 ∨ c = -1 := by
    rcases hr with h | h
    · exact Int.eq_one_or_neg_one_of_mul_eq_one ((all r).symm.trans h)
    · apply Int.eq_one_or_neg_one_of_mul_eq_one (v := -L r)
      have hh := (all r).symm.trans h
      linear_combination -hh
  rcases hc with h | h
  · exact Or.inl (funext fun i => by simpa only [h,one_mul] using all i)
  · exact Or.inr (funext fun i => by simpa only [h,neg_one_mul] using all i)

end MollinWalshPrime

/-! Assemble after the Hamilton identities and the `SignedPerm` definition. -/

namespace MollinWalshPrime

private theorem signedSquareSum {ι : Type*} [Fintype ι] (q : ι → ℤ)
    (σ : Equiv.Perm ι) (ε : ι → Bool) :
    (∑ i, (if ε i then -q (σ i) else q (σ i)) ^ 2) = ∑ i, (q i) ^ 2 := by
  calc
    _ = ∑ i, (q (σ i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : ε i <;> simp [h]
    _ = _ := Equiv.sum_comp σ (fun i ↦ (q i) ^ 2)

theorem norm4_of_signedPerm {q r : V4} (h : SignedPerm q r) : norm4 r = norm4 q := by
  obtain ⟨σ, ε, hr⟩ := h
  have hr' : r = fun i ↦ if ε i then -q (σ i) else q (σ i) := funext hr
  rw [hr']
  exact signedSquareSum q σ ε

theorem norm3_of_signedPerm (v : V3) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    norm3 (fun i ↦ if ε i then -v (σ i) else v (σ i)) = norm3 v :=
  signedSquareSum v σ ε

theorem rotate_modEq36 (q r : V4) (w : V3)
    (hr : ∀ i, Int.ModEq 36 (q i) (r i)) (i : Fin 3) :
    Int.ModEq 36 (rotate q w i) (rotate r w i) := by
  have hc (j : Fin 4) : (q j : ZMod 36) = (r j : ZMod 36) :=
    (ZMod.intCast_eq_intCast_iff _ _ 36).mpr (hr j)
  apply (ZMod.intCast_eq_intCast_iff _ _ 36).mp
  fin_cases i <;> simp [rotate, hc]

theorem representation_of_residue_rotation {m p : ℤ} (q r : V4) (w : V3)
    (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool)
    (hq : norm4 q = p) (hw : norm3 w = 6 * m)
    (hr : ∀ i, Int.ModEq 36 (q i) (r i))
    (good : let R := rotate r w
            let v : V3 := fun i ↦ if ε i then -R (σ i) else R (σ i)
            (18 : ℤ) ∣ v 0 + v 1 ∧ (12 : ℤ) ∣ v 0 - v 1 + v 2 ∧
              (6 : ℤ) ∣ v 0 - v 1 - 2 * v 2) :
    ∃ x s z : ℤ, p ^ 2 * m = x ^ 2 + 8 * s ^ 2 + 27 * z ^ 2 := by
  let v : V3 := fun i ↦ if ε i then -rotate q w (σ i) else rotate q w (σ i)
  let u : V3 := fun i ↦ if ε i then -rotate r w (σ i) else rotate r w (σ i)
  change (18 : ℤ) ∣ u 0 + u 1 ∧ (12 : ℤ) ∣ u 0 - u 1 + u 2 ∧
    (6 : ℤ) ∣ u 0 - u 1 - 2 * u 2 at good
  have hu (i : Fin 3) : Int.ModEq 36 (v i) (u i) := by
    have h := rotate_modEq36 q r w hr (σ i)
    cases he : ε i
    · simpa [v, u, he] using h
    · simpa [v, u, he] using h.neg
  apply represent_of_rotation q w v hq hw (norm3_of_signedPerm (rotate q w) σ ε)
  · exact ((Int.ModEq.of_dvd (by decide : (18 : ℤ) ∣ 36) ((hu 0).add (hu 1))).dvd_iff).mpr good.1
  · exact ((Int.ModEq.of_dvd (by decide : (12 : ℤ) ∣ 36)
      (((hu 0).sub (hu 1)).add (hu 2))).dvd_iff).mpr good.2.1
  · exact ((Int.ModEq.of_dvd (by decide : (6 : ℤ) ∣ 36)
      (((hu 0).sub (hu 1)).sub (Int.ModEq.mul_left 2 (hu 2)))).dvd_iff).mpr good.2.2

end MollinWalshPrime

namespace MollinWalshPrime

-- Compiled after MWHamilton, MWLines, MWLiftStep, and the modular rotation bridge.
private def bcSeeds : ℕ → List V3
  | 7 => [
      ![4,1,5], ![4,(-5),(-1)], ![5,(-1),4], ![5,(-1),(-4)],
      ![1,(-5),4], ![4,(-1),(-5)], ![4,5,1], ![1,(-4),5],
      ![5,4,1], ![1,5,(-4)], ![5,1,4], ![1,4,(-5)],
      ![5,(-4),(-1)], ![4,5,(-1)], ![4,(-5),1], ![1,4,5],
      ![1,(-4),(-5)], ![5,1,(-4)], ![1,5,4], ![1,(-5),(-4)],
      ![4,1,(-5)], ![4,(-1),5]]
  | 15 => [
      ![9,0,3], ![3,0,9], ![0,9,3], ![8,1,5],
      ![8,(-5),(-1)], ![4,5,7], ![4,(-7),(-5)], ![5,(-1),8],
      ![8,(-1),5], ![4,(-5),7], ![7,(-5),4], ![4,5,(-7)],
      ![5,(-7),4], ![1,(-5),8], ![8,1,(-5)]]
  | 23 => [
      ![1,4,11], ![1,(-11),(-4)], ![1,(-4),11], ![11,4,1],
      ![4,(-11),1], ![4,1,(-11)], ![1,11,4], ![11,1,(-4)],
      ![1,11,(-4)], ![4,11,(-1)], ![1,4,(-11)], ![4,1,11],
      ![1,(-4),(-11)], ![4,(-1),(-11)], ![4,(-11),(-1)], ![1,(-11),4]]
  | 87 => [
      ![9,0,21], ![21,0,9], ![0,9,21], ![8,17,13],
      ![8,(-13),(-17)], ![20,1,11], ![20,(-11),(-1)], ![8,(-17),13],
      ![8,13,(-17)], ![20,(-1),(-11)], ![20,11,1], ![1,(-11),(-20)],
      ![11,(-1),20], ![13,(-17),(-8)], ![17,(-13),8]]
  | 111 => [
      ![0,15,21], ![4,25,5], ![4,(-5),(-25)], ![24,9,3],
      ![24,3,(-9)], ![24,(-9),3], ![24,3,9], ![4,5,(-25)],
      ![4,(-25),5], ![15,0,21], ![3,9,24], ![3,9,(-24)],
      ![4,5,25], ![4,(-5),25]]
  | 119 => [
      ![13,23,(-4)], ![5,25,(-8)], ![25,5,8], ![5,(-17),(-20)],
      ![17,(-5),(-20)], ![4,(-13),23], ![8,(-25),(-5)], ![8,5,25],
      ![13,4,23], ![5,(-25),(-8)], ![25,(-5),8], ![4,13,(-23)],
      ![5,8,(-25)], ![5,(-8),(-25)]]
  | _ => []

private def bcPerm3 (i : Fin 3) : Equiv.Perm (Fin 3) :=
  if i = 0 then ⟨![1,2,0], ![2,0,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩
  else if i = 1 then ⟨![2,0,1], ![1,2,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩
  else Equiv.refl _

private def bcPerms4 : List (Equiv.Perm (Fin 4)) := [
  ⟨![0,1,2,3], ![0,1,2,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![0,1,3,2], ![0,1,3,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![0,2,1,3], ![0,2,1,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![0,2,3,1], ![0,3,1,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![0,3,1,2], ![0,2,3,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![0,3,2,1], ![0,3,2,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![1,0,2,3], ![1,0,2,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![1,0,3,2], ![1,0,3,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![1,2,0,3], ![2,0,1,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![1,2,3,0], ![3,0,1,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![1,3,0,2], ![2,0,3,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![1,3,2,0], ![3,0,2,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![2,0,1,3], ![1,2,0,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![2,0,3,1], ![1,3,0,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![2,1,0,3], ![2,1,0,3], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![2,1,3,0], ![3,1,0,2], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![2,3,0,1], ![2,3,0,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![2,3,1,0], ![3,2,0,1], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![3,0,1,2], ![1,2,3,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![3,0,2,1], ![1,3,2,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![3,1,0,2], ![2,1,3,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![3,1,2,0], ![3,1,2,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![3,2,0,1], ![2,3,1,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩,
  ⟨![3,2,1,0], ![3,2,1,0], by intro i; fin_cases i <;> rfl, by intro i; fin_cases i <;> rfl⟩]

private def bcSign3 (c : Fin 4) (i : Fin 3) : Bool :=
  if i = 1 then c.val.testBit 0 else if i = 2 then c.val.testBit 1 else false

private def bcAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (ε : Fin n → Bool)
    (q : Fin n → ℤ) : Fin n → ℤ := fun i => if ε i then -q (σ i) else q (σ i)

private def bcLattice (v : V3) : Prop :=
  (18 : ℤ) ∣ v 0+v 1 ∧ (12 : ℤ) ∣ v 0-v 1+v 2 ∧ (6 : ℤ) ∣ v 0-v 1-2*v 2

private instance (v : V3) : Decidable (bcLattice v) := inferInstanceAs
  (Decidable ((18 : ℤ) ∣ v 0+v 1 ∧ (12 : ℤ) ∣ v 0-v 1+v 2 ∧ (6 : ℤ) ∣ v 0-v 1-2*v 2))

private def bcOrder (w : V3) : Equiv.Perm (Fin 3) :=
  bcPerm3 (if w 0 % 2 = 0 then 0 else if w 1 % 2 = 0 then 1 else 2)

private def bcSuccess (r : V4) (m : ℕ) : Bool :=
  (bcSeeds m).any fun w => decide (norm3 w = 6*(m : ℤ)) &&
    (List.finRange 4).any fun c => decide (bcLattice (bcAct (bcOrder w) (bcSign3 c) (rotate r w)))

/-- A base-5 histogram of the four absolute remainders modulo nine. -/
private def bcDigit (z : ℤ) : ℕ := (min (z % 9) ((-z) % 9)).toNat

private def bcKey (q : V4) : ℕ := ∑ i, 5 ^ bcDigit (q i)

private def bcRoughKeys (m : ℕ) : List ℕ :=
  match m with
  | 7 => [8,28,32,628,632,652]
  | 15 => [8,28,628]
  | 23 => [8,12,20,28,52,100,132,136,152,176,256,276,380,400,628,752,876,1000,1252,1376,2500]
  | 87 => [8,28,628]
  | 111 => [8,28,628]
  | 119 => [8,28,628]
  | _ => []

private def bcRough (m : ℕ) (q : V4) : Bool := (bcRoughKeys m).contains (bcKey q)

private def bcInput {n : ℕ} (a b c d : Fin n) : V4 :=
  ![(a.val : ℤ), (b.val : ℤ), (c.val : ℤ), (d.val : ℤ)]

private def bcKernels : Fin 6 → ℕ := ![7,15,23,87,111,119]

private lemma bc_kernel {m : ℕ} (hm : m ∈ ({7,15,23,87,111,119} : Finset ℕ)) :
    ∃ e : Fin 6, bcKernels e = m := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩

private lemma bc_direct_computation (a b c d : Fin 19) (e : Fin 6)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (ho : norm4 (bcInput a b c d) % 2 = 1)
    (h3 : norm4 (bcInput a b c d) % 3 ≠ 0) :
    bcRough (bcKernels e) (bcInput a b c d) = true ∨
    bcSuccess (bcInput a b c d) (bcKernels e) = true := by
  revert e d c b
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
    fin_cases a <;> decide +kernel

private def bcNormals : List V4 := [
  ![0,1,(-2),(-1)], ![0,1,(-2),1], ![0,1,(-1),(-2)], ![0,1,(-1),2],
  ![0,1,1,(-2)], ![0,1,1,2], ![0,1,2,(-1)], ![0,1,2,1],
  ![0,2,(-1),(-1)], ![0,2,(-1),1], ![0,2,1,(-1)], ![0,2,1,1],
  ![1,(-2),(-1),0], ![1,(-2),0,(-1)], ![1,(-2),0,1], ![1,(-2),1,0],
  ![1,(-1),(-2),0], ![1,(-1),0,(-2)], ![1,(-1),0,2], ![1,(-1),2,0],
  ![1,0,(-2),(-1)], ![1,0,(-2),1], ![1,0,(-1),(-2)], ![1,0,(-1),2],
  ![1,0,1,(-2)], ![1,0,1,2], ![1,0,2,(-1)], ![1,0,2,1],
  ![1,1,(-2),0], ![1,1,0,(-2)], ![1,1,0,2], ![1,1,2,0],
  ![1,2,(-1),0], ![1,2,0,(-1)], ![1,2,0,1], ![1,2,1,0],
  ![2,(-1),(-1),0], ![2,(-1),0,(-1)], ![2,(-1),0,1], ![2,(-1),1,0],
  ![2,0,(-1),(-1)], ![2,0,(-1),1], ![2,0,1,(-1)], ![2,0,1,1],
  ![2,1,(-1),0], ![2,1,0,(-1)], ![2,1,0,1], ![2,1,1,0]]

private def bcReflect (q v : V4) : V4 := fun i => q i - (dot4 q v / 3)*v i

private def bcEscape (m : ℕ) (r : V4) : Bool :=
  bcNormals.any fun v => decide (norm4 v = 6 ∧ (3 : ℤ) ∣ dot4 r v) &&
    !(bcRough m (bcReflect r v))

private def bcOrbit (L : V4) : List V4 :=
  bcPerms4.flatMap fun σ => (List.finRange 16).map fun c =>
    bcAct σ (fun i => c.val.testBit i.val) L

private lemma bcOrbit_sound {L M : V4} (h : M ∈ bcOrbit L) : SignedPerm L M := by
  obtain ⟨σ, _, hσ⟩ := List.mem_flatMap.mp h
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hσ
  exact ⟨σ, fun i => c.val.testBit i.val, fun _ => rfl⟩

private instance (r L : V4) (n : ℕ) : Decidable (Near r L n) :=
  inferInstanceAs (Decidable (∀ i j : Fin 4, (n : ℤ) ∣ r i*L j-r j*L i))

private def bcFinal (m : ℕ) (splitCase : Bool) (r : V4) : Bool :=
  (lineSeeds m splitCase).any fun L => (bcOrbit L).any fun M =>
    decide (Near r M (if splitCase then 9 else 27))

private lemma bcFinal_sound {m : ℕ} {splitCase : Bool} {r : V4} (h : bcFinal m splitCase r = true) :
    ∃ L, allowedLine m splitCase L ∧ Near r L (if splitCase then 9 else 27) := by
  obtain ⟨L, hL, hh⟩ := List.any_eq_true.mp h
  obtain ⟨M, hM, hn⟩ := List.any_eq_true.mp hh
  exact ⟨M, ⟨L, hL, bcOrbit_sound hM⟩, of_decide_eq_true hn⟩

private lemma bc_reflect_computation (a b c d : Fin 14) (e : Fin 6)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (h3 : norm4 (bcInput a b c d) % 3 ≠ 0)
    (hr : bcRough (bcKernels e) (bcInput a b c d) = true) :
    bcEscape (bcKernels e) (bcInput a b c d) = true ∨
    bcFinal (bcKernels e) (norm4 (bcInput a b c d) % 3 == 1) (bcInput a b c d) = true := by
  revert e d c b
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
    fin_cases a <;> decide +kernel

private def bcCoordinate (n z : ℤ) : ℤ := min (z%n) ((-z)%n)

private lemma bc_normalize (q : V4) (n : ℤ)
    (hn : 0 < n)
    (hbound : ∀ z : ℤ, 0 ≤ bcCoordinate n z ∧ bcCoordinate n z ≤ n/2) :
    ∃ x : V4, SignedPerm q x ∧ Monotone (fun i => x i % n) ∧
      ∀ i, 0 ≤ x i % n ∧ x i % n ≤ n/2 := by
  let f : Fin 4 → ℤ := fun i => bcCoordinate n (q i)
  let σ := Tuple.sort f
  let ε : Fin 4 → Bool := fun i => decide ((-q (σ i))%n < q (σ i)%n)
  let x := bcAct σ ε q
  have he (i : Fin 4) : x i % n = f (σ i) := by
    dsimp only [x, bcAct, ε, f, bcCoordinate]
    by_cases h : (-q (σ i))%n < q (σ i)%n
    · simp [h, min_eq_right (le_of_lt h)]
    · simp [h, min_eq_left (le_of_not_gt h)]
  refine ⟨x, ⟨σ, ε, fun _ => rfl⟩, ?_, ?_⟩
  · intro i j hij
    rw [he, he]
    exact Tuple.monotone_sort f hij
  · intro i
    rw [he]
    exact hbound _

private lemma bc_mod_norm (q r : V4) (n : ℤ) (h : ∀ i, Int.ModEq n (q i) (r i)) :
    Int.ModEq n (norm4 q) (norm4 r) := by
  rw [norm4_coords, norm4_coords]
  exact ((((h 0).pow 2).add ((h 1).pow 2)).add ((h 2).pow 2)).add ((h 3).pow 2)

private lemma bc_dot_congr (q r v : V4) (n : ℤ) (h : ∀ i, Int.ModEq n (q i) (r i)) :
    Int.ModEq n (dot4 q v) (dot4 r v) := by
  have hdot (a : V4) : dot4 a v = a 0*v 0+a 1*v 1+a 2*v 2+a 3*v 3 := by
    simp [dot4, Fin.sum_univ_succ, add_assoc]
  rw [hdot, hdot]
  exact ((((h 0).mul_right _).add ((h 1).mul_right _)).add ((h 2).mul_right _)).add
    ((h 3).mul_right _)

private lemma bc_key_congr (x y : V4) (h : ∀ i, Int.ModEq 9 (x i) (y i)) : bcKey x = bcKey y := by
  apply Finset.sum_congr rfl
  intro i _
  have hneg := (h i).neg
  change (-(x i))%9 = (-(y i))%9 at hneg
  have hi := h i
  change x i % 9 = y i % 9 at hi
  simp [bcDigit, hi, hneg]

private lemma bc_key_signed {q r : V4} (h : SignedPerm q r) : bcKey q = bcKey r := by
  rcases h with ⟨σ, ε, hσ⟩
  have hh (i : Fin 4) : bcDigit (r i) = bcDigit (q (σ i)) := by
    rw [hσ i]
    cases ε i <;> simp [bcDigit, min_comm]
  calc
    bcKey q = ∑ i, 5 ^ bcDigit (q (σ i)) := (σ.sum_comp _).symm
    _ = bcKey r := by simp [bcKey, hh]

private lemma bc_rough_congr (m : ℕ) (x y : V4) (h : ∀ i, Int.ModEq 9 (x i) (y i)) :
    bcRough m x = bcRough m y := by
  simp only [bcRough, bc_key_congr x y h]

private lemma bc_rough_signed (m : ℕ) {x y : V4} (h : SignedPerm x y) :
    bcRough m x = bcRough m y := by
  simp only [bcRough, bc_key_signed h]

private lemma bc_bound {n : ℤ} (hn : 0 < n) (z : ℤ) :
    0 ≤ bcCoordinate n z ∧ bcCoordinate n z ≤ n/2 := by
  have h0 := Int.emod_nonneg z (ne_of_gt hn)
  have h1 := Int.emod_lt_of_pos z hn
  have hz : (-z)%n = (n-z%n)%n := by
    rw [Int.sub_emod_emod, ← Int.neg_emod_eq_sub_emod]
  by_cases h : z%n=0
  · simp [bcCoordinate, hz, h] <;> omega
  · have hred : (n-z%n)%n = n-z%n := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hred] at hz
    simp only [bcCoordinate, hz, le_min_iff, min_le_iff]
    omega

private lemma bc_pack (q : V4) (n : ℤ) (k : ℕ) (hm : Monotone (fun i => q i%n))
    (hb : ∀ i, 0 ≤ q i%n ∧ q i%n < (k:ℤ)) :
    ∃ a b c d : Fin k, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      ∀ i, Int.ModEq n (q i) (bcInput a b c d i) := by
  let t (i : Fin 4) : Fin k := ⟨(q i%n).toNat, by have hh := hb i; omega⟩
  have ht (i : Fin 4) : ((t i).val : ℤ) = q i%n := Int.toNat_of_nonneg (hb i).1
  have mono {i j : Fin 4} (hij : i ≤ j) : t i ≤ t j := by
    change (q i%n).toNat ≤ (q j%n).toNat
    exact Int.toNat_le_toNat (hm hij)
  refine ⟨t 0, t 1, t 2, t 3, mono (by decide), mono (by decide), mono (by decide), ?_⟩
  intro i
  have hi : bcInput (t 0) (t 1) (t 2) (t 3) i = q i%n := by
    fin_cases i <;> first | exact ht _ | rfl
  rw [hi]
  change q i%n = (q i%n)%n
  simp

private lemma bc_prime3 {p : ℕ} (hp : p.Prime) (hb : 31 < p) : p%3 ≠ 0 := by
  intro h
  have hh := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
  omega

private lemma bc_rough_of_failure {m p : ℕ} (hm : m ∈ ({7,15,23,87,111,119} : Finset ℕ))
    (hp : p.Prime) (hbig : 31 < p)
    (hbad : ¬∃ x s z : ℤ, (p : ℤ)^2*m = x^2+8*s^2+27*z^2)
    (q : V4) (hq : norm4 q = (p : ℤ)) : bcRough m q = true := by
  obtain ⟨e, he⟩ := bc_kernel hm
  obtain ⟨x, hsp, hmono, hbound⟩ :=
    bc_normalize q 36 (by decide) (bc_bound (by decide))
  have hx : norm4 x = (p:ℤ) := (norm4_of_signedPerm hsp).trans hq
  obtain ⟨a,b,c,d,hab,hbc,hcd,hr⟩ := bc_pack x 36 19 hmono (fun i => by
    have hi := hbound i
    omega)
  let r := bcInput a b c d
  have hnorm := bc_mod_norm x r 36 hr
  rw [hx] at hnorm
  have hpodd := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 := bc_prime3 hp hbig
  have h2 : norm4 r % 2 = 1 := by
    have hx2 := hnorm.of_dvd (show (2:ℤ) ∣ 36 by decide)
    change (p:ℤ)%2 = norm4 r%2 at hx2
    omega
  have h3 : norm4 r % 3 ≠ 0 := by
    have hx3 := hnorm.of_dvd (show (3:ℤ) ∣ 36 by decide)
    change (p:ℤ)%3 = norm4 r%3 at hx3
    omega
  have hf := bc_direct_computation a b c d e hab hbc hcd h2 h3
  rw [he] at hf
  rcases hf with hrough | hsuccess
  · rw [bc_rough_signed m hsp, bc_rough_congr m x r (fun i => (hr i).of_dvd (by decide))]
    exact hrough
  · obtain ⟨w, _, hw⟩ := List.any_eq_true.mp hsuccess
    obtain ⟨hw', hoc⟩ := Bool.and_eq_true_iff.mp hw
    obtain ⟨c', _, hc'⟩ := List.any_eq_true.mp hoc
    exact False.elim (hbad (representation_of_residue_rotation x r w (bcOrder w) (bcSign3 c')
      hx (of_decide_eq_true hw') hr (of_decide_eq_true hc')))

private lemma bc_reflect_congr (q r v : V4) (hr : ∀ i, Int.ModEq 27 (q i) (r i))
    (hd : (3:ℤ) ∣ dot4 r v) :
    (3 : ℤ) ∣ dot4 q v ∧ ∀ i, Int.ModEq 9 (bcReflect q v i) (bcReflect r v i) := by
  have hh := bc_dot_congr q r v 27 hr
  have hdiv : (3:ℤ) ∣ dot4 q v := ((hh.of_dvd (by decide : (3:ℤ) ∣ 27)).dvd_iff).mpr hd
  refine ⟨hdiv, ?_⟩
  have hquot : Int.ModEq 9 (dot4 q v / 3) (dot4 r v / 3) := by
    have hq := Int.modEq_iff_dvd.mp hh
    apply Int.modEq_iff_dvd.mpr
    omega
  intro i
  exact ((hr i).of_dvd (by decide)).sub (hquot.mul_right (v i))

theorem base_classification {m p : ℕ} (hm : m ∈ ({7,15,23,87,111,119} : Finset ℕ))
    (hp : p.Prime) (hbig : 31 < p)
    (hbad : ¬∃ x s z : ℤ, (p : ℤ)^2*m = x^2+8*s^2+27*z^2)
    (q : V4) (hq : norm4 q=(p:ℤ)) :
    ∃ L, allowedLine m (p%3==1) L ∧ Near q L (nearBase p) := by
  obtain ⟨e, he⟩ := bc_kernel hm
  obtain ⟨x, hsp, hmono, hbound⟩ :=
    bc_normalize q 27 (by decide) (bc_bound (by decide))
  have hx : norm4 x = (p:ℤ) := (norm4_of_signedPerm hsp).trans hq
  obtain ⟨a,b,c,d,hab,hbc,hcd,hr⟩ := bc_pack x 27 14 hmono (fun i => by
    have hi := hbound i
    omega)
  let r := bcInput a b c d
  have hnorm := bc_mod_norm x r 27 hr
  rw [hx] at hnorm
  have hx3 := hnorm.of_dvd (show (3:ℤ) ∣ 27 by decide)
  change (p:ℤ)%3 = norm4 r%3 at hx3
  have hp3 := bc_prime3 hp hbig
  have h3 : norm4 r % 3 ≠ 0 := by omega
  have hrough : bcRough m r = true := by
    rw [← bc_rough_congr m x r (fun i => (hr i).of_dvd (by decide))]
    exact bc_rough_of_failure hm hp hbig hbad x hx
  have hc := bc_reflect_computation a b c d e hab hbc hcd h3 (by simpa only [he] using hrough)
  rw [he] at hc
  rcases hc with escape | line
  · obtain ⟨v, _, hesc⟩ := List.any_eq_true.mp escape
    obtain ⟨hv, hf⟩ := Bool.and_eq_true_iff.mp hesc
    obtain ⟨hv6, hd⟩ := of_decide_eq_true hv
    have hh := bc_reflect_congr x r v hr hd
    have hnr : norm4 (bcReflect x v) = (p:ℤ) :=
      (reflection_norm x v (dot4 x v / 3) hv6 (by have := hh.1; omega)).trans hx
    have hgood := bc_rough_of_failure hm hp hbig hbad (bcReflect x v) hnr
    rw [bc_rough_congr m _ _ hh.2] at hgood
    simp [hgood] at hf
  · have hs : (norm4 r % 3 == 1) = (p%3==1) := by
      by_cases hp1 : p%3 = 1
      · have h1 : norm4 r%3 = 1 := by omega
        simp [h1, hp1]
      · have h1 : norm4 r%3 ≠ 1 := by omega
        simp [h1, hp1]
    change bcFinal m (norm4 r%3==1) r = true at line
    rw [hs] at line
    obtain ⟨L, hL, hnear⟩ := bcFinal_sound line
    have hbase : (if (p%3==1) then 9 else 27 : ℕ) = nearBase p := by
      by_cases h : p%3=1 <;> simp [nearBase, h]
    rw [hbase] at hnear
    have hdiv : ((nearBase p : ℕ):ℤ) ∣ 27 := by
      unfold nearBase
      split <;> decide
    have hxnear : Near x L (nearBase p) := by
      intro i j
      have hh := ((hr i).mul_right (L j)).sub ((hr j).mul_right (L i))
      exact ((hh.of_dvd hdiv).dvd_iff).mpr (hnear i j)
    exact pull_near_signed hsp hL hxnear

end MollinWalshPrime

namespace MollinWalshPrime

theorem exceptional_prime_ternary {m p : ℕ} (hm : m ∈ ({7,15,23,87,111,119} : Finset ℕ))
    (hp : p.Prime) (hbig : 31<p) :
    ∃ x s z : ℤ, (p : ℤ)^2*m=x^2+8*s^2+27*z^2 := by
  classical
  by_contra hbad
  let splitCase := (p%3==1)
  let R : ℕ := if splitCase then 3 else 9
  have casesR : R=3 ∨ R=9 := by dsimp only [R]; split <;> simp
  have heq : nearBase p=3*R := by
    by_cases h : p%3=1 <;> simp [nearBase,R,splitCase,h]
  have div3 : ¬(3 : ℤ) ∣ (p : ℤ) := by
    intro h
    have h' : 3 ∣ p := by exact_mod_cast h
    rcases (Nat.dvd_prime hp).mp h' with h' | h' <;> omega
  have base : ∀ q : V4, norm4 q=(p : ℤ) →
      ∃ L, allowedLine m splitCase L ∧ Near q L (3*R) := by
    intro q hq
    rw [← heq]
    exact base_classification hm hp hbig hbad q hq
  have hsep : ∀ L K, allowedLine m splitCase L → allowedLine m splitCase K →
      Near L K R → K=L ∨ K=fun i => -L i := by
    intro L K hL hK hnear
    exact allowedLine_separated hL hK hnear
  obtain ⟨q,hq⟩ := exists_norm4_nat p
  have all := iterated_lift casesR div3 (fun _ h => allowedLine_pivot h)
    (fun _ h => allowedLine_normals h) hsep base q hq
  obtain ⟨F, hF⟩ := allowedLine_finset m splitCase
  apply MWExactLine.impossible_exceptional_family hp hbig (q := q) hq (F := F)
    (fun L h => allowedLine_norm ((hF L).mp h))
    (fun L h => allowedLine_pivot ((hF L).mp h))
  intro k _
  obtain ⟨L,hL,hN⟩ := all k
  exact ⟨L,(hF L).mpr hL,hN⟩

end MollinWalshPrime

theorem OMA.solution : OMA.R_oeis_a056828_R1.H2 := by
  intro m hm p hp hbig
  obtain ⟨x,s,z,h⟩ := MollinWalshPrime.exceptional_prime_ternary hm hp hbig
  exact MollinWalshPrime.powerful_of_ternary (n := p^2*m) (by push_cast; exact h)

import Mathlib

/-!
# Square divisors along consecutive doublings in OEIS A300984

At input p, F evaluated with a = 2^(i+1) is the nonsquarefree-divisor
sum for 2^i p² when i ≥ 2 and p is an odd prime. The same prime square
q² with q ≥ 5 cannot divide two such sums less than twenty exponents
apart. The prime p = 37 realizes a gap of twenty for q = 5.
Proof by Codex for @dwilfand-sys, checked in Lean 4.37.0-rc1.
Source: https://oeis.org/A300984
-/

namespace DoublingPatterns

def F (a x : ℤ) : ℤ := a*(x^2+x+1)-(x+2)^2

theorem bezout (a b x : ℤ) :
    ((x+3)-b*x)*F a x - ((x+3)-a*x)*F b x = 3*(a-b) := by unfold F; ring

theorem common_divisor {a b x d : ℤ} (ha : d ∣ F a x) (hb : d ∣ F b x) :
    d ∣ 3*(a-b) := by
  rw [← bezout a b x]
  exact dvd_sub (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hb _)

theorem collision {i t : ℕ} {x d : ℤ}
    (h1 : d ∣ F (2^(i+t+1)) x) (h0 : d ∣ F (2^(i+1)) x) :
    d ∣ 3*2^(i+1)*(2^t-1) := by
  have h := common_divisor h1 h0
  rw [show i+t+1 = (i+1)+t by omega, pow_add] at h
  convert h using 1; ring

theorem local_witness (a : ℤ) : F a (-2) = 3*a := by unfold F; ring

theorem discriminant (a : ℤ) : (a-4)^2-4*(a-1)*(a-4) = -3*a*(a-4) := by ring

private def smallGapOK : Bool := (List.range 20).all fun t => (List.range 725).all fun q =>
  decide (0<t → 5≤q → ¬ q^2 ∣ 2^t-1)
set_option maxHeartbeats 900000 in
private theorem gapTable : smallGapOK = true := by decide +kernel

theorem gap_squarefree {t q : ℕ} (ht : 0<t) (hu : t≤19) (hq : 5≤q) : ¬ q^2 ∣ 2^t-1 := by
  intro hd
  have htpos : 1 < 2^t := Nat.one_lt_pow (by omega) (by decide)
  have hl := Nat.le_of_dvd (by omega : 0 < 2^t-1) hd
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hu
  have qb : q<725 := by
    by_contra! hq7
    have hh := Nat.pow_le_pow_left hq7 2
    norm_num at hh hpow
    omega
  have tc := List.all_eq_true.mp gapTable t (List.mem_range.mpr (by omega))
  have qc := List.all_eq_true.mp tc q (List.mem_range.mpr qb)
  exact (of_decide_eq_true qc : 0<t → 5≤q → ¬ q^2 ∣ 2^t-1) ht hq hd

theorem disjoint_obstructions {i t q : ℕ} {x : ℤ} (ht : 0<t) (hu : t≤19) (hq : q.Prime) (hq5 : 5≤q)
    (hi : (q:ℤ)^2 ∣ F (2^(i+1)) x) (hj : (q:ℤ)^2 ∣ F (2^(i+t+1)) x) : False := by
  have he := collision hj hi
  have pos : 1 ≤ (2:ℕ)^t := Nat.one_le_pow _ _ (by decide)
  have natdiv : q^2 ∣ 3*2^(i+1)*(2^t-1) := by
    exact_mod_cast (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub pos,Nat.cast_ofNat,Nat.cast_one] using he : ((q^2:ℕ):ℤ) ∣ ((3*2^(i+1)*(2^t-1):ℕ):ℤ))
  have c2 := (Nat.coprime_primes hq Nat.prime_two).mpr (by omega)
  have c3 := (Nat.coprime_primes hq (by decide : Nat.Prime 3)).mpr (by omega)
  have c : (q^2).Coprime (3*2^(i+1)) := (c3.mul_right (c2.pow_right _)).pow_left _
  exact gap_squarefree ht hu hq5 (c.dvd_of_dvd_mul_left natdiv)
theorem obstruction_at_gap_twenty : (25 : ℤ) ∣ F (2^(6+1)) 37 ∧ (25 : ℤ) ∣ F (2^(26+1)) 37 := by
  norm_num [F]
#print axioms obstruction_at_gap_twenty
#print axioms disjoint_obstructions
#print axioms collision
#print axioms local_witness
end DoublingPatterns

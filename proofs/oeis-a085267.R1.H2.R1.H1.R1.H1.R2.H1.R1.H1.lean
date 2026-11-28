import OMAReductions.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R2_H1_R1
import Mathlib

/-!
# A085267 intermediate prime-square cost certificate

Source: https://oeis.org/A085267
Credit: @dwilfand-sys. The original sequence statement was formalized by @niclorusso.

The argument gives a uniform bound for odd-prime costs using inclusion-exclusion on the integers coprime to the first 26 primes.
-/

open scoped BigOperators

namespace A085267Sieve

def largePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => 2 < p ∧ Nat.Prime p)

def largeRho (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1-1/(p:ℚ))

end A085267Sieve

namespace A085267InclusionExclusion

/-- Repeatedly subtract the contribution of multiples of the next divisor. -/
def sift (ps : List ℕ) (F : ℕ → ℚ) (d : ℕ) : ℚ :=
  match ps with
  | [] => F d
  | p :: rest => sift rest F d - sift rest F (d*p)

def density (ps : List ℕ) : ℚ :=
  (ps.map fun p => 1 - 1 / (p : ℚ)).prod

theorem sift_main (ps : List ℕ) (X : ℚ) (d : ℕ) :
    sift ps (fun t => X / (t : ℚ)) d = X / d * density ps := by
  induction ps generalizing d with
  | nil => simp [sift, density]
  | cons p rest ih =>
    change sift rest (fun t => X / (t : ℚ)) d -
      sift rest (fun t => X / (t : ℚ)) (d*p) = _
    rw [ih d, ih (d*p)]
    change X / (d : ℚ) * density rest - X / ((d*p : ℕ) : ℚ) * density rest =
      X / (d : ℚ) * ((1 - 1 / (p : ℚ)) * density rest)
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring

theorem sift_shift (ps : List ℕ) (F : ℕ → ℚ) (c : ℚ) (d : ℕ) :
    sift ps (fun t => F t + c) d = sift ps F d + (if ps = [] then c else 0) := by
  induction ps generalizing d with
  | nil => simp [sift]
  | cons p rest ih => simp [sift, ih] <;> ring

/-- A pointwise unit error for each squarefree divisor contributes at most one
unit for each subset of the prime divisors. Only divisors of d times the
listed product are needed. -/
theorem sift_error (ps : List ℕ) (F H : ℕ → ℚ) (E : ℚ) (d : ℕ)
    (h : ∀ t : ℕ, t ∣ d*ps.prod → |F t - H t| ≤ E) :
    |sift ps F d - sift ps H d| ≤ (2:ℚ)^ps.length * E := by
  induction ps generalizing d with
  | nil => simpa [sift] using h d (by simp)
  | cons p rest ih =>
    have hd : d * rest.prod ∣ d * (p :: rest).prod := ⟨p, by simp only [List.prod_cons]; ring⟩
    have hleft := ih d (fun t ht => h t (ht.trans hd))
    have hright := ih (d*p) (fun t ht => h t (by simpa [Nat.mul_assoc] using ht))
    obtain ⟨hl, hu⟩ := abs_le.mp hleft
    obtain ⟨hl', hu'⟩ := abs_le.mp hright
    simp only [sift, List.length_cons, pow_succ]
    apply abs_le.mpr
    constructor <;> linarith

theorem sift_sum {α : Type*} (s : Finset α) (ps : List ℕ) (F : α → ℕ → ℚ) (d : ℕ) :
    sift ps (fun t => ∑ x ∈ s, F x t) d = ∑ x ∈ s, sift ps (F x) d := by
  induction ps generalizing d with
  | nil => rfl
  | cons p rest ih => simp only [sift, ih, Finset.sum_sub_distrib]

/-- Sieving the indicator of divisibility gives the indicator of divisibility
and coprimality to the sieving product. -/
theorem sift_indicator (ps : List ℕ) (x d : ℕ) (hpair : ps.Pairwise Nat.Coprime)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hd : ∀ p ∈ ps, d.Coprime p) :
    sift ps (fun t => if t ∣ x then 1 else 0) d =
      if d ∣ x ∧ ps.prod.Coprime x then 1 else 0 := by
  induction ps generalizing d with
  | nil => simp [sift]
  | cons p rest ih =>
    obtain ⟨hpr, hr⟩ := List.pairwise_cons.mp hpair
    have hprime := hp p (by simp)
    have hdp := hd p (by simp)
    have hprimes : ∀ q ∈ rest, Nat.Prime q := fun q hq => hp q (by simp [hq])
    have hcop : ∀ q ∈ rest, d.Coprime q := fun q hq => hd q (by simp [hq])
    have hcop' : ∀ q ∈ rest, (d*p).Coprime q := fun q hq =>
      (hcop q hq).mul_left (hpr q hq)
    have hmul : d*p ∣ x ↔ d ∣ x ∧ p ∣ x := by
      constructor
      · intro hh
        exact ⟨(Nat.dvd_mul_right d p).trans hh, (Nat.dvd_mul_left p d).trans hh⟩
      · rintro ⟨h1,h2⟩
        exact hdp.mul_dvd_of_dvd_of_dvd h1 h2
    simp only [sift, ih d hr hprimes hcop, ih (d*p) hr hprimes hcop',
      List.prod_cons, Nat.coprime_mul_iff_left, hprime.coprime_iff_not_dvd, hmul]
    by_cases h1 : d ∣ x <;> by_cases h2 : p ∣ x <;> by_cases h3 : rest.prod.Coprime x <;>
      simp [h1,h2,h3]

/-- In particular, if the number of multiples of each d in a candidate set
is within E of X/d, imposing coprimality changes the main term to X times
the proportion of units, with error at most 2^r times E. -/
theorem coprime_values_error_centered {α : Type*} (s : Finset α) (v : α → ℕ)
    (ps : List ℕ) (X c E : ℚ)
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (h : ∀ d : ℕ, d ∣ ps.prod →
      |(∑ x ∈ s, if d ∣ v x then (1:ℚ) else 0) - (X/d + c)| ≤ E) :
    |(∑ x ∈ s, if ps.prod.Coprime (v x) then (1:ℚ) else 0)
        - (X * density ps + if ps = [] then c else 0)|
      ≤ (2:ℚ)^ps.length * E := by
  have bound := sift_error ps (fun d => ∑ x ∈ s, if d ∣ v x then (1:ℚ) else 0)
    (fun t => X / (t : ℚ) + c) E 1 (fun t ht => h t (by simpa using ht))
  rw [sift_sum, sift_shift, sift_main] at bound
  have hind (x : ℕ) : sift ps (fun t => if t ∣ x then 1 else 0) 1 =
      if ps.prod.Coprime x then 1 else 0 := by
    simpa using sift_indicator ps x 1 hpair hp (fun p _ => Nat.coprime_one_left p)
  simpa only [hind, Nat.cast_one, div_one] using bound

theorem coprime_count_error_centered (s : Finset ℕ) (ps : List ℕ) (X c E : ℚ)
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (h : ∀ d : ℕ, d ∣ ps.prod →
      |(∑ x ∈ s, if d ∣ x then (1:ℚ) else 0) - (X/d + c)| ≤ E) :
    |(∑ x ∈ s, if ps.prod.Coprime x then (1:ℚ) else 0)
        - (X * density ps + if ps = [] then c else 0)|
      ≤ (2:ℚ)^ps.length * E :=
  coprime_values_error_centered s id ps X c E hpair hp h

theorem coprime_count_error (s : Finset ℕ) (ps : List ℕ) (X E : ℚ)
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (h : ∀ d : ℕ, d ∣ ps.prod →
      |(∑ x ∈ s, if d ∣ x then (1:ℚ) else 0) - X/d| ≤ E) :
    |(∑ x ∈ s, if ps.prod.Coprime x then (1:ℚ) else 0) - X * density ps|
      ≤ (2:ℚ)^ps.length * E := by
  simpa using coprime_count_error_centered s ps X 0 E hpair hp (by simpa using h)

end A085267InclusionExclusion

namespace A085267Cost

open A085267InclusionExclusion

/-- Legendre's finite sieve with a cutoff when the divisor exceeds the interval. -/
def fastSift (ps : List ℕ) (x d : ℕ) : ℤ :=
  match ps with
  | [] => ((x/d : ℕ) : ℤ)
  | p::rest => if x < d then 0 else fastSift rest x d - fastSift rest x (d*p)

/-- The same sieve indexed by the remaining interval length. -/
def qSift : List Nat → Nat → Int
  | [], y => (y : Int)
  | p :: ps, y =>
      if y = 0 then 0 else qSift ps y - qSift ps (y / p)

theorem fastSift_eq_qSift (ps : List Nat) (x : Nat) :
    ∀ d : Nat, 0 < d → (∀ p ∈ ps, 0 < p) →
      fastSift ps x d = qSift ps (x / d) := by
  induction ps with
  | nil =>
      intro d _ _
      rfl
  | cons p ps ih =>
      intro d hd hpos
      have hp : 0 < p := hpos p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (by simp [hq])
      by_cases h : x < d
      · simp [fastSift, qSift, h, Nat.div_eq_of_lt h]
      · have hdx : d ≤ x := by omega
        have hy : x / d ≠ 0 := (Nat.div_pos hdx hd).ne'
        simp only [fastSift, if_neg h, qSift, if_neg hy, ih d hd htail,
          ih (d * p) (Nat.mul_pos hd hp) htail, Nat.div_div_eq_div_mul]

private theorem sift_empty_interval (ps : List ℕ) (x d : ℕ) (h : x < d)
    (hp : ∀ p ∈ ps, 0 < p) : sift ps (fun t => ((x/t : ℕ) : ℚ)) d = 0 := by
  induction ps generalizing d with
  | nil => simp [sift, Nat.div_eq_of_lt h]
  | cons p rest ih =>
    have hrest : ∀ q ∈ rest, 0 < q := fun q hq => hp q (by simp [hq])
    have hp1 := hp p (by simp)
    have hmul : d ≤ d*p := by simpa using Nat.mul_le_mul_left d hp1
    rw [sift,ih d h hrest,ih (d*p) (h.trans_le hmul) hrest,sub_zero]

theorem fastSift_cast (ps : List ℕ) (x d : ℕ) (hp : ∀ p ∈ ps, 0 < p) :
    (fastSift ps x d : ℚ) = sift ps (fun t => ((x/t : ℕ):ℚ)) d := by
  induction ps generalizing d with
  | nil => simp only [fastSift, sift, Int.cast_natCast]
  | cons p rest ih =>
    have hrest : ∀ q ∈ rest, 0 < q := fun q hq => hp q (by simp [hq])
    by_cases h : x < d
    · simp [fastSift,h,sift_empty_interval (p::rest) x d h hp]
    · simp [fastSift,sift,h,ih d hrest,ih (d*p) hrest]

theorem rough_card (ps : List ℕ) (x : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hpair : ps.Pairwise Nat.Coprime) :
    (((Finset.Ioc 0 x).filter (fun k => ps.prod.Coprime k)).card : ℤ) = fastSift ps x 1 := by
  have counts (d : ℕ) : ((x/d : ℕ):ℚ) = ∑ k ∈ Finset.Ioc 0 x, if d ∣ k then (1:ℚ) else 0 := by
    rw [Finset.sum_boole, Nat.Ioc_filter_dvd_card_eq_div]
  have h : (fastSift ps x 1 : ℚ) =
      (((Finset.Ioc 0 x).filter (fun k => ps.prod.Coprime k)).card : ℚ) := by
    rw [fastSift_cast ps x 1 (fun p h => (hp p h).pos)]
    simp only [counts,sift_sum]
    simp only [sift_indicator ps _ 1 hpair hp (fun p _ => Nat.coprime_one_left p),
      one_dvd,true_and,Finset.sum_boole]
  exact_mod_cast h.symm

def wheel : List ℕ :=
  [101,97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2]

set_option maxRecDepth 20000 in
private theorem wheel_complete : ∀ p : Fin 102, 2 < p.val → Nat.Prime p.val →
    p.val ∈ wheel.toFinset.erase 2 := by decide +kernel

theorem odd_prime_count_upper (x : ℕ) (hx : 101 ≤ x) :
    ((((Finset.range (x+1)).filter (fun p => 2 < p ∧ p.Prime)).card : ℤ)) ≤
      fastSift wheel x 1 + 24 := by
  let rough := (Finset.Ioc 0 x).filter (fun k => wheel.prod.Coprime k)
  let known := wheel.toFinset.erase 2
  have facts : ∀ p ∈ wheel, Nat.Prime p ∧ p ≤ 101 := by decide
  have hp : ∀ p ∈ wheel, Nat.Prime p := fun _ h => (facts _ h).1
  have hknown : known.card = 25 := by decide
  have hone : 1 ∈ rough := by simp [rough,Finset.mem_Ioc] <;> omega
  have hsub : (Finset.range (x+1)).filter (fun p => 2 < p ∧ p.Prime) ⊆
      known ∪ rough.erase 1 := by
    intro p h
    obtain ⟨hx',h₂,hp'⟩ := Finset.mem_filter.mp h
    have hpx := Finset.mem_range.mp hx'
    by_cases hsmall : p ≤ 101
    · exact Finset.mem_union_left _ (wheel_complete ⟨p,by omega⟩ h₂ hp')
    · apply Finset.mem_union_right
      apply Finset.mem_erase.mpr
      refine ⟨by omega,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,?_⟩⟩
      apply Nat.coprime_list_prod_left_iff.mpr
      intro q hq
      apply Nat.Coprime.symm
      apply hp'.coprime_iff_not_dvd.mpr
      intro hdiv
      have := Nat.le_of_dvd (hp q hq).pos hdiv
      have := (facts q hq).2
      omega
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hknown,Finset.card_erase_of_mem hone] at hc
  have hp1 := Finset.card_pos.mpr ⟨1,hone⟩
  have hval : (rough.card : ℤ) = fastSift wheel x 1 :=
    rough_card wheel x hp (by decide)
  omega

def primeDeltas (j : ℕ) : ℕ :=
  ∑ p ∈ (Finset.range 1415).filter (fun p => 2 < p ∧ p.Prime), 2*j/(p^2)

def costUpper (j : ℕ) : ℤ := fastSift wheel (2*j+1) 1 + 24 + primeDeltas j

theorem cost_upper (j : ℕ) (hlo : 300 ≤ j) (hhi : j ≤ 1000000) :
    ((∑ p ∈ (Finset.range (2*j+2)).filter (fun p => 2 < p ∧ p.Prime),
      ((2*j)/(p^2)+1) : ℕ):ℤ) ≤ costUpper j := by
  let P := (Finset.range (2*j+2)).filter (fun p => 2 < p ∧ p.Prime)
  let Q := (Finset.range 1415).filter (fun p => 2 < p ∧ p.Prime)
  have outside (p : ℕ) (hp : p ∈ P \ Q) : 2*j/(p^2) = 0 := by
    obtain ⟨hmem,hn⟩ := Finset.mem_sdiff.mp hp
    have hpp := (Finset.mem_filter.mp hmem).2
    have hbig : 1415 ≤ p := by
      by_contra! h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h,hpp⟩)
    apply Nat.div_eq_of_lt
    have hp2 := Nat.pow_le_pow_left hbig 2
    omega
  have hfloor : (∑ p ∈ P, 2*j/(p^2)) ≤ primeDeltas j := by
    have remove : (∑ p ∈ P \ Q, 2*j/(p^2)) = 0 := Finset.sum_eq_zero outside
    have add := Finset.sum_sdiff (f := fun p => 2*j/(p^2))
      (show P ∩ Q ⊆ P from Finset.inter_subset_left)
    have eq : P \ (P ∩ Q) = P \ Q := by ext p; simp <;> tauto
    rw [eq, remove, zero_add] at add
    rw [← add]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    exact fun _ _ _ => Nat.zero_le _
  have hcard := odd_prime_count_upper (2*j+1) (by omega)
  change (P.card : ℤ) ≤ _ at hcard
  change ((∑ p ∈ P, (2*j/(p^2)+1) : ℕ):ℤ) ≤ _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_add]
  change ((∑ p ∈ P, 2*j/(p^2) : ℕ) : ℤ) + (P.card : ℤ) ≤ costUpper j
  have hf : ((∑ p ∈ P, 2*j/(p^2) : ℕ) : ℤ) ≤ (primeDeltas j : ℤ) := by
    exact_mod_cast hfloor
  unfold costUpper
  omega


private theorem qSift_zero' (ps : List ℕ) : qSift ps 0 = 0 := by
  cases ps <;> simp [qSift]

private theorem qSift_fold (ps : List ℕ) (y : ℕ) :
    qSift ps y = ps.foldr (fun p (g : ℕ → ℤ) x => g x - g (x/p)) (fun x => (x:ℤ)) y := by
  induction ps generalizing y with
  | nil => rfl
  | cons p ps ih =>
    change qSift (p :: ps) y = _ - _
    rw [← ih, ← ih]
    by_cases hy : y = 0
    · simp [qSift,hy,qSift_zero']
    · simp [qSift,hy]

theorem costUpper_fold (j : ℕ) :
    costUpper j =
      wheel.foldr (fun p (g : ℕ → ℤ) x => g x - g (x/p)) (fun x => (x:ℤ)) (2*j+1) +
      24 + (primeDeltas j : ℤ) := by
  have hw : ∀ p ∈ wheel, 0 < p := by decide
  rw [costUpper, fastSift_eq_qSift wheel (2*j+1) 1 (by decide) hw, Nat.div_one, qSift_fold]

end A085267Cost

theorem OMA.solution : OMA.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R2_H1_R1.H1 := by
  dsimp only [OMA.R_oeis_a085267_R1_H2_R1_H1_R1_H1_R2_H1_R1.H1]
  intro j hlo hhi
  have hj := A085267Cost.cost_upper j hlo hhi
  rw [A085267Cost.costUpper_fold] at hj
  exact hj

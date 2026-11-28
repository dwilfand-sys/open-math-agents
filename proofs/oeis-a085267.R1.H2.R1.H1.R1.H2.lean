import OMAReductions.R_oeis_a085267_R1_H2_R1_H1_R1
import Mathlib

/-!
# A middle-range obstruction for two square-plus-squarefree representations

Source: https://oeis.org/A085267
Credit: @dwilfand-sys (proof prepared by Codex).

If at most one square root works, at most one retained parity index can
produce a squarefree remainder. Every other retained index is covered by
an odd prime-square obstruction. The resulting inequality is the reverse
of the separate numerical budget.
-/

open scoped BigOperators

namespace A085265Sieve

def largePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun p => 2 < p ∧ Nat.Prime p)

def largeRho (S : Finset ℕ) : ℚ := ∏ p ∈ S, (1-1/(p:ℚ))

end A085265Sieve

namespace A085265InclusionExclusion

open A085265Sieve

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

/-- Count the progression r, r+m, ... strictly below J. -/
theorem residue_card (m J r : ℕ) (hm : 0 < m) (hr : r < m) :
    ((Finset.range J).filter (fun x => x % m = r)).card =
      J/m + if r < J%m then 1 else 0 := by
  let c := J/m + if r < J%m then 1 else 0
  let f (i : ℕ) := r+i*m
  have hJ := Nat.div_add_mod' J m
  have hrem := Nat.mod_lt J hm
  have hlt (i : ℕ) : i < c ↔ f i < J := by
    dsimp [c,f]
    rcases lt_trichotomy i (J/m) with hi | he | hi
    · have hg : (i+1)*m ≤ (J/m)*m := Nat.mul_le_mul_right m hi
      rw [Nat.add_mul, one_mul] at hg
      split_ifs <;> omega
    · rw [he]
      split_ifs <;> omega
    · have hg : (J/m+1)*m ≤ i*m := Nat.mul_le_mul_right m hi
      rw [Nat.add_mul, one_mul] at hg
      split_ifs <;> omega
  have hs : (Finset.range J).filter (fun x => x % m = r) = (Finset.range c).image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
      have hv : f (x/m) = x := by
        have hv := Nat.mod_add_div' x m
        simpa only [f,he] using hv
      exact Finset.mem_image.mpr ⟨x/m, Finset.mem_range.mpr
        ((hlt _).mpr (by rw [hv]; exact Finset.mem_range.mp hx)), hv⟩
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((hlt i).mp (Finset.mem_range.mp hi)),
        by simp [f,Nat.add_mod,Nat.mod_eq_of_lt hr]⟩
  have hf : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    have he : i*m = j*m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm he
  rw [hs, Finset.card_image_of_injective _ hf, Finset.card_range]

private theorem dvd_double_rem (d x b : ℕ) :
    d ∣ 2*x+b ↔ d ∣ 2*(x%d)+b := by
  have hx := Nat.div_add_mod' x d
  have he : 2*x+b = (2*(x/d))*d + (2*(x%d)+b) := by nlinarith
  rw [he]
  exact Nat.dvd_add_right (Nat.dvd_mul_left d _)

private theorem odd_divisor_even_roots {d : ℕ} (hd : Odd d) (x : ℕ) :
    d ∣ 2*x+2 ↔ x%d=d-1 := by
  obtain ⟨v,hv⟩ := hd
  have hdpos : 0 < d := by omega
  have hrem := Nat.mod_lt x hdpos
  rw [dvd_double_rem]
  constructor
  · intro h
    by_contra hne
    have hh := Nat.eq_of_dvd_of_lt_two_mul (by omega : 2*(x%d)+2 ≠ 0) h (by omega)
    omega
  · intro he
    refine ⟨2, ?_⟩
    omega

private theorem odd_divisor_odd_roots {d v : ℕ} (hv : d=2*v+1) (x : ℕ) :
    d ∣ 2*x+1 ↔ x%d=v := by
  have hdpos : 0 < d := by omega
  have hrem := Nat.mod_lt x hdpos
  rw [dvd_double_rem]
  constructor
  · intro h
    have hh := Nat.eq_of_dvd_of_lt_two_mul (by omega : 2*(x%d)+1 ≠ 0) h (by omega)
    omega
  · intro he
    rw [he, ← hv]

/-- The initial progression of even roots has an error of at most one half
after centering its main term by subtracting one half. -/
theorem even_divisor_error {d : ℕ} (hd : Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if d ∣ 2*x+2 then (1:ℚ) else 0) -
      ((J:ℚ)/d - 1/2)| ≤ 1/2 := by
  obtain ⟨v,hv⟩ := hd
  have hdpos : 0 < d := by omega
  have hr := Nat.mod_lt J hdpos
  have hn : ¬ d-1 < J%d := by omega
  simp_rw [odd_divisor_even_roots (show Odd d from ⟨v,hv⟩)]
  rw [Finset.sum_boole, residue_card d J (d-1) hdpos (by omega), if_neg hn, Nat.add_zero]
  have hJ := Nat.div_add_mod' J d
  have hlow : ((J/d:ℕ):ℚ)*(d:ℚ) ≤ J := by
    exact_mod_cast (show (J/d)*d ≤ J by omega)
  have hhigh : (J:ℚ) ≤ (((J/d:ℕ):ℚ)+1)*(d:ℚ) := by
    exact_mod_cast (show J ≤ (J/d+1)*d by rw [Nat.add_mul,one_mul]; omega)
  have hpos : (0:ℚ) < d := by exact_mod_cast hdpos
  have h1 := (le_div_iff₀ hpos).mpr hlow
  have h2 := (div_le_iff₀ hpos).mpr hhigh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- In the odd progression the admissible class is centered in every block. -/
theorem odd_divisor_error {d : ℕ} (hd : Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if d ∣ 2*x+1 then (1:ℚ) else 0) -
      (J:ℚ)/d| ≤ 1/2 := by
  obtain ⟨v,hv⟩ := hd
  have hdv : d=2*v+1 := by omega
  have hdpos : 0 < d := by omega
  have hr := Nat.mod_lt J hdpos
  have hJ := Nat.div_add_mod' J d
  simp_rw [odd_divisor_odd_roots hdv]
  rw [Finset.sum_boole, residue_card d J v hdpos (by omega)]
  let C := J/d + if v < J%d then 1 else 0
  have hlow : 2*J ≤ (2*C+1)*d := by
    dsimp [C]
    split_ifs with ht
    · nlinarith
    · nlinarith
  have hhigh : 2*C*d ≤ 2*J+d := by
    dsimp [C]
    split_ifs with ht
    · nlinarith
    · simp only [Nat.add_zero, Nat.mul_assoc]
      omega
  have hl : 2*(J:ℚ) ≤ (2*(C:ℚ)+1)*(d:ℚ) := by exact_mod_cast hlow
  have hu : 2*(C:ℚ)*(d:ℚ) ≤ 2*(J:ℚ)+(d:ℚ) := by exact_mod_cast hhigh
  have hpos : (0:ℚ) < d := by exact_mod_cast hdpos
  have h1 : (J:ℚ)/d ≤ (C:ℚ)+1/2 := (div_le_iff₀ hpos).mpr (by nlinarith only [hl])
  have h2 : (C:ℚ)-1/2 ≤ (J:ℚ)/d := (le_div_iff₀ hpos).mpr (by nlinarith only [hu])
  change |(C:ℚ)-(J:ℚ)/d| ≤ 1/2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem initial_even_coprime (ps : List ℕ) (hne : ps ≠ [])
    (hpair : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, Nat.Prime p)
    (hd : ∀ d : ℕ, d ∣ ps.prod → Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if ps.prod.Coprime (2*x+2) then (1:ℚ) else 0) -
      (J:ℚ)*density ps| ≤ (2:ℚ)^ps.length / 2 := by
  have h := coprime_values_error_centered (Finset.range J) (fun x => 2*x+2) ps J
    (-(1/2)) (1/2) hpair hp (fun d hf => by
      simpa only [sub_eq_add_neg] using even_divisor_error (hd d hf) J)
  simpa [hne,div_eq_mul_inv] using h

theorem initial_odd_coprime (ps : List ℕ) (hpair : ps.Pairwise Nat.Coprime)
    (hp : ∀ p ∈ ps, Nat.Prime p) (hd : ∀ d : ℕ, d ∣ ps.prod → Odd d) (J : ℕ) :
    |(∑ x ∈ Finset.range J, if ps.prod.Coprime (2*x+1) then (1:ℚ) else 0) -
      (J:ℚ)*density ps| ≤ (2:ℚ)^ps.length / 2 := by
  have h := coprime_values_error_centered (Finset.range J) (fun x => 2*x+1) ps J
    0 (1/2) hpair hp (fun d hf => by simpa using odd_divisor_error (hd d hf) J)
  simpa [div_eq_mul_inv] using h

/-- Below the modulus the two roots are an opposite pair. The assumption
that p² does not divide n suffices, including primes dividing n exactly once. -/
private theorem root_or_opposite {n p a b : ℕ}
    (hp : p.Prime) (hp2 : 2<p) (hn : ¬p^2 ∣ n) (hab : a≤b)
    (ha : a^2 ≡ n [MOD p^2]) (hb : b^2 ≡ n [MOD p^2]) :
    p^2 ∣ b-a ∨ p^2 ∣ a+b := by
  let d := b-a
  have hba : b=a+d := by dsimp [d]; omega
  have hs : b^2=a^2+d*(a+b) := by rw [hba]; ring
  have hdiv := (ha.trans hb.symm).dvd'
  rw [hs,Nat.add_sub_cancel_left] at hdiv
  by_cases hd : p ∣ d
  · left
    have hcop : p.Coprime (a+b) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hu
      have h2a : p ∣ 2*a := by
        have he : a+b-d=2*a := by omega
        simpa only [he] using Nat.dvd_sub hu hd
      have hpa : p ∣ a := (hp.dvd_mul.mp h2a).resolve_left
        (fun h => (not_le.mpr hp2) (Nat.le_of_dvd (by decide) h))
      obtain ⟨t,ht⟩ := hpa
      have haa : p^2 ∣ a^2 := ⟨t^2,by rw [ht]; ring⟩
      exact hn (Nat.modEq_zero_iff_dvd.mp (ha.symm.trans haa.modEq_zero_nat))
    exact (hcop.pow_left 2).dvd_of_dvd_mul_right hdiv
  · right
    exact ((hp.coprime_iff_not_dvd.mpr hd).pow_left 2).dvd_of_dvd_mul_left hdiv

/-- Candidates have the form 2x+b, where x starts at zero and b=1 or 2.
The entire bin [t p²,(t+1)p²) contains at most one candidate root. -/
theorem raw_prime_loss {n p b J : ℕ} (hp : p.Prime) (hp2 : 2<p) (hn : ¬p^2 ∣ n)
    (hb : b ≤ 2) :
    ((Finset.range J).filter (fun x => (2*x+b)^2 ≡ n [MOD p^2])).card ≤ 2*J/(p^2)+1 := by
  let A := (Finset.range J).filter (fun x => (2*x+b)^2 ≡ n [MOD p^2])
  let f (x : ℕ) := (2*x+b)/(p^2)
  let bins := Finset.range (2*J/(p^2)+1)
  have hm : 0<p^2 := pow_pos hp.pos 2
  have hcop : (p^2).Coprime 2 := ((hp.odd_of_ne_two (by omega)).pow.coprime_two_left).symm
  have inj {x y : ℕ} (hx : x∈A) (hy : y∈A) (hxy : x≤y) (hf : f x=f y) : x=y := by
    have hs := root_or_opposite hp hp2 hn (show 2*x+b ≤ 2*y+b by omega)
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    change (2*x+b)/(p^2)=(2*y+b)/(p^2) at hf
    by_contra hne
    have bounds {L M : ℕ} (lo : L ≤ 2*x+b) (hi : 2*y+b < L+M) :
        (0 < y-x ∧ y-x < M) ∧ (0 < x+y+b-L ∧ x+y+b-L < M) := by omega
    have hi : 2*y+b < ((2*x+b)/(p^2))*(p^2) + p^2 := by
      calc
        2*y+b < (p^2)*((2*y+b)/(p^2)+1) := Nat.lt_mul_div_succ _ hm
        _ = _ := by rw [← hf]; ring
    obtain ⟨hdiff,hmid⟩ := bounds (Nat.div_mul_le_self (2*x+b) (p^2)) hi
    rcases hs with hd | hsum
    · have he : 2*y+b-(2*x+b)=2*(y-x) := by omega
      rw [he] at hd
      exact (Nat.not_le_of_lt hdiff.2) (Nat.le_of_dvd hdiff.1 (hcop.dvd_of_dvd_mul_left hd))
    · have he : (2*x+b)+(2*y+b)=2*(x+y+b) := by omega
      rw [he] at hsum
      have hv := hcop.dvd_of_dvd_mul_left hsum
      have hbase : p^2 ∣ ((2*x+b)/(p^2))*(p^2) := Nat.dvd_mul_left _ _
      have hh := Nat.dvd_sub hv hbase
      exact (Nat.not_le_of_lt hmid.2) (Nat.le_of_dvd hmid.1 hh)
  have hc : A.card ≤ bins.card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (show 2*x+b ≤ 2*J by omega)))
    · intro x hx y hy he
      rcases le_total x y with h | h
      · exact inj hx hy h he
      · exact (inj hy hx h he.symm).symm
  simpa only [A,bins,Finset.card_range] using hc

def candidateSet (ps : List ℕ) (J b : ℕ) :=
  (Finset.range J).filter (fun x => ps.prod.Coprime (2*x+b))

def hitSet (n p : ℕ) (ps : List ℕ) (J b : ℕ) :=
  (candidateSet ps J b).filter (fun x => (2*x+b)^2 ≡ n [MOD p^2])

theorem hit_card_raw {n p b J : ℕ} (ps : List ℕ) (hp : p.Prime) (hp2 : 2<p)
    (hn : ¬p^2 ∣ n) (hb : b≤2) : (hitSet n p ps J b).card ≤ 2*J/(p^2)+1 := by
  apply le_trans (Finset.card_le_card ?_) (raw_prime_loss hp hp2 hn hb)
  intro x hx
  obtain ⟨hx,hcon⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hcon⟩

structure PrimeEnumeration (S : Finset ℕ) where
  ps : List ℕ
  pair : ps.Pairwise Nat.Coprime
  mem : ∀ p, p ∈ ps ↔ p ∈ S
  len : ps.length = S.card
  product : ps.prod = ∏ p ∈ S, p
  rho : density ps = largeRho S

theorem prime_enumeration (S : Finset ℕ) (hS : ∀ p ∈ S, 2<p ∧ p.Prime) :
    Nonempty (PrimeEnumeration S) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⟨[],by simp,by simp,by simp,by simp,by simp [density,largeRho]⟩⟩
  | @insert a S ha ih =>
    obtain ⟨D⟩ := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
    have hpa := (hS a (Finset.mem_insert_self a S)).2
    refine ⟨⟨a::D.ps, List.pairwise_cons.mpr ⟨?_,D.pair⟩, ?_, ?_, ?_, ?_⟩⟩
    · intro q hq
      have hqm := (D.mem q).mp hq
      exact (Nat.coprime_primes hpa (hS q (Finset.mem_insert_of_mem hqm)).2).mpr (by
        rintro rfl; exact ha hqm)
    · intro p
      simp [D.mem]
    · simp [ha,D.len]
    · simp [ha,D.product]
    · change (1 - 1 / (a : ℚ)) * density D.ps = largeRho (insert a S)
      rw [D.rho]
      simp only [largeRho, Finset.prod_insert ha]

private theorem odd_product_list (ps : List ℕ) (h : ∀ p ∈ ps, Odd p) : Odd ps.prod := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    exact (h p (by simp)).mul (ih (fun q hq => h q (by simp [hq])))

theorem prime_divisor_odd {S : Finset ℕ} (D : PrimeEnumeration S)
    (hS : ∀ p ∈ S, 2<p ∧ p.Prime) {d : ℕ} (hd : d ∣ D.ps.prod) : Odd d := by
  have ho := odd_product_list D.ps (fun p hp => by
    obtain ⟨h2,hpr⟩ := hS p ((D.mem p).mp hp)
    exact hpr.odd_of_ne_two (by omega))
  apply Nat.odd_iff.mpr
  by_contra he
  have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
  exact ho.not_two_dvd_nat (h2.trans hd)

def initialError (r : ℕ) : ℚ := if r=0 then 0 else (2:ℚ)^(r-1)

theorem initial_candidates {S : Finset ℕ} (D : PrimeEnumeration S) (b J : ℕ)
    (hS : ∀ p ∈ S, 2<p ∧ p.Prime) (hb : b=1 ∨ b=2) :
    (J:ℚ)*largeRho S - initialError S.card ≤ ((candidateSet D.ps J b).card:ℚ) := by
  classical
  have hp : ∀ p ∈ D.ps, p.Prime := fun p hm => (hS p ((D.mem p).mp hm)).2
  have hd : ∀ d : ℕ, d ∣ D.ps.prod → Odd d := fun _ he => prime_divisor_odd D hS he
  by_cases he : D.ps=[]
  · have hsc : S.card=0 := by simpa only [←D.len,he,List.length_nil]
    have hr : largeRho S=1 := by rw [←D.rho,he]; simp [density]
    simp [candidateSet,he,hsc,hr,initialError]
  · have hlen : 0<D.ps.length := by
      cases h : D.ps with
      | nil => exact False.elim (he h)
      | cons p ps => simp
    have hspos : 0<S.card := by rw [← D.len]; exact hlen
    have hhalf : (2:ℚ)^D.ps.length/2 = initialError S.card := by
      rw [D.len,initialError,if_neg (by omega)]
      conv_lhs => rw [show S.card=S.card-1+1 by omega,pow_succ]
      ring
    have hh : |((candidateSet D.ps J b).card:ℚ) - (J:ℚ)*largeRho S|
        ≤ initialError S.card := by
      rcases hb with rfl | rfl
      · have hh := initial_odd_coprime D.ps D.pair hp hd J
        simpa only [Finset.sum_boole,D.rho,hhalf,candidateSet] using hh
      · have hh := initial_even_coprime D.ps he D.pair hp hd J
        simpa only [Finset.sum_boole,D.rho,hhalf,candidateSet] using hh
    have := (abs_le.mp hh).1
    linarith

theorem candidate_card_le_good_add_hits {n J b : ℕ} {S : Finset ℕ} (D : PrimeEnumeration S)
    (hreg : ∀ p : ℕ, 2<p → p.Prime → (p∈S ↔ p^2∣n))
    (hb : b=1 ∨ b=2) (hfit : ∀ x<J, (2*x+b)^2<n)
    (hupper : (n-1).sqrt ≤ 2*J+1) (hpar : ∀ x<J, ¬4∣n-(2*x+b)^2) :
    (candidateSet D.ps J b).card ≤
      ((Finset.range J).filter (fun x => Squarefree (n-(2*x+b)^2))).card +
      ∑ p ∈ (largePrimeSet (2*J+1)) \ S, (hitSet n p D.ps J b).card := by
  classical
  let good := (Finset.range J).filter (fun x => Squarefree (n-(2*x+b)^2))
  let P := (largePrimeSet (2*J+1)) \ S
  have sub : candidateSet D.ps J b ⊆ good ∪ P.biUnion (fun p => hitSet n p D.ps J b) := by
    intro x hx
    obtain ⟨hr,hc⟩ := Finset.mem_filter.mp hx
    have hlt := Finset.mem_range.mp hr
    have hsq := hfit x hlt
    by_cases hbad : Squarefree (n-(2*x+b)^2)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr,hbad⟩)
    apply Finset.mem_union_right
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push_neg at hbad
    obtain ⟨p,hp,hpd⟩ := hbad
    have hd : p^2 ∣ n-(2*x+b)^2 := by simpa only [pow_two] using hpd
    have h2 : 2<p := by
      have := hp.two_le
      by_contra! hh
      have he : p=2 := by omega
      exact hpar x hlt (by simpa [he] using hpd)
    have hnmem : p∉S := by
      intro hpS
      have hpn := (hreg p h2 hp).mp hpS
      have hdiff := Nat.dvd_sub hpn hd
      have hback : n-(n-(2*x+b)^2)=(2*x+b)^2 := by omega
      rw [hback] at hdiff
      have hpk : p ∣ 2*x+b := by
        have hh : p ∣ (2*x+b)*(2*x+b) :=
          (Nat.dvd_mul_right p p).trans (by simpa only [pow_two] using hdiff)
        exact (hp.dvd_mul.mp hh).elim id id
      have hbprod : p ∣ D.ps.prod := by rw [D.product]; exact Finset.dvd_prod_of_mem id hpS
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hbprod hpk hc
    have ple := Nat.le_of_dvd (show 0<n-(2*x+b)^2 by omega) hd
    have hroot : p ≤ (n-1).sqrt := Nat.le_sqrt'.mpr (by
      have hk : 0<2*x+b := by rcases hb with rfl | rfl <;> omega
      have := pow_pos hk 2
      omega)
    have hpmem : p∈largePrimeSet (2*J+1) := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),h2,hp⟩
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hpmem,hnmem⟩,
      Finset.mem_filter.mpr ⟨hx,Nat.modEq_of_dvd' hsq.le hd⟩⟩
  calc
    _ ≤ (good ∪ P.biUnion (fun p => hitSet n p D.ps J b)).card := Finset.card_le_card sub
    _ ≤ good.card + (P.biUnion (fun p => hitSet n p D.ps J b)).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _


end A085265InclusionExclusion

open A085265Sieve A085265InclusionExclusion OMA.S_oeis_a085267

private theorem square_product_dvd (n : ℕ) (S : Finset ℕ)
    (h : ∀ p ∈ S, p.Prime ∧ p^2 ∣ n) : (∏ p ∈ S,p)^2 ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p T hp ih =>
    obtain ⟨pp,hd⟩ := h p (by simp)
    have hT : ∀ q ∈ T, q.Prime ∧ q^2 ∣ n := fun q hq => h q (by simp [hq])
    have hc : p.Coprime (∏ q ∈ T,q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply pp.coprime_iff_not_dvd.mpr
      exact fun hd => hp (((Nat.prime_dvd_prime_iff_eq pp (hT q hq).1).mp hd).symm ▸ hq)
    rw [Finset.prod_insert hp,mul_pow]
    exact ((hc.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd hd (ih hT)

theorem OMA.solution : OMA.R_oeis_a085267_R1_H2_R1_H1_R1.H2 := by
  classical
  intro n hlo hhi failure
  have hn : 0 < n := by omega
  let u := (n-1).sqrt
  let e : ℕ := if 4 ∣ n then 1 else 0
  let b : ℕ := if 4 ∣ n then 1 else 2
  let J := (u+e)/2
  let S := (Finset.range (n+1)).filter (fun p => 2<p ∧ p.Prime ∧ p^2∣n)
  have hu : 600 ≤ u := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hJ : 300 ≤ J := by dsimp only [J]; omega
  have hutop : u < 2000000 := by
    by_contra! h
    have hs : 4000000000000 ≤ n-1 := Nat.le_sqrt'.mp (show 2000000 ≤ (n-1).sqrt from h)
    omega
  have hJtop : J ≤ 1000000 := by
    have he : e ≤ 1 := by dsimp [e]; split <;> omega
    dsimp only [J]
    omega
  have hupper : (n-1).sqrt ≤ 2*J+1 := by change u ≤ 2*((u+e)/2)+1; omega
  have hb : b=1 ∨ b=2 := by unfold b; split <;> simp
  have hfit (x : ℕ) (hx : x<J) : (2*x+b)^2 < n := by
    have hku : 2*x+b ≤ u := by
      by_cases hc : 4∣n <;> simp only [J,b,e,hc,if_true,if_false] at hx ⊢ <;> omega
    have hs := Nat.le_sqrt'.mp hku
    omega
  have hS : ∀ p ∈ S, 2<p ∧ p.Prime := by
    intro p hp
    obtain ⟨_,hl,pp,_⟩ := Finset.mem_filter.mp hp
    exact ⟨hl,pp⟩
  have hreg (p : ℕ) (hl : 2<p) (pp : p.Prime) : p∈S ↔ p^2∣n := by
    constructor
    · exact fun hp => (Finset.mem_filter.mp hp).2.2.2
    · intro hp
      have hpn : p ∣ n := (show p ∣ p^2 by simp [pow_two]).trans hp
      have := Nat.le_of_dvd hn hpn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hl,pp,hp⟩
  have hd := square_product_dvd n S (fun p hp => ⟨(hS p hp).2,(Finset.mem_filter.mp hp).2.2.2⟩)
  have hB : (∏ p ∈ S,p) ≤ 2*J+2 := by
    have hsq := Nat.le_of_dvd hn hd
    have hn' : n ≤ (u+1)^2 := by
      have := Nat.lt_succ_sqrt' (n-1)
      change n-1 < (u+1)^2 at this
      omega
    have hbu : (∏ p ∈ S,p) ≤ u+1 := by
      by_contra! hh
      have hbig := Nat.pow_le_pow_left (show u+2 ≤ ∏ p ∈ S,p by omega) 2
      nlinarith
    change u ≤ 2*J+1 at hupper
    omega
  have hpar (x : ℕ) (hx : x<J) : ¬4∣n-(2*x+b)^2 := by
    intro hbad
    have hlt := hfit x hx
    by_cases hc : 4∣n
    · have hs := Nat.dvd_sub hc hbad
      rw [show n-(n-(2*x+b)^2)=(2*x+b)^2 by omega] at hs
      have hb' : b=1 := by simp [b,hc]
      rw [hb',show (2*x+1)^2=4*(x*(x+1))+1 by ring] at hs
      omega
    · have hb' : b=2 := by simp [b,hc]
      have hs : 4 ∣ (2*x+b)^2 := ⟨(x+1)^2,by rw [hb']; ring⟩
      exact hc (by simpa only [Nat.sub_add_cancel hlt.le] using dvd_add hbad hs)
  refine ⟨J, S, hJ, hJtop, hS, hB, ?_⟩
  let good := (Finset.range J).filter fun x => Squarefree (n-(2*x+b)^2)
  let roots := (Finset.range (n.sqrt + 1)).filter fun w =>
    0 < w ∧ w^2 < n ∧ Squarefree (n-w^2)
  let emb : ℕ ↪ ℕ := ⟨fun x => 2*x+b, by
    intro x y h
    change 2*x+b = 2*y+b at h
    omega⟩
  have sub : good.map emb ⊆ roots := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨hxr,hs⟩ := Finset.mem_filter.mp hx
    have hsq := hfit x (Finset.mem_range.mp hxr)
    have hsqrt : 2*x+b ≤ n.sqrt := Nat.le_sqrt'.mpr hsq.le
    change 2*x+b ∈ (Finset.range (n.sqrt + 1)).filter _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, hsq, hs⟩
  have heq : roots.card = representations n := by
    unfold representations
    apply congrArg Finset.card
    ext w
    simp only [roots, Finset.mem_filter]
  have hle : good.card ≤ representations n := by
    simpa only [Finset.card_map, heq] using (Finset.card_le_card sub)
  have hone : good.card ≤ 1 := by omega
  obtain ⟨D⟩ := prime_enumeration S hS
  let P := (largePrimeSet (2*J+1)) \ S
  have cover := candidate_card_le_good_add_hits D hreg hb hfit hupper hpar
  change (candidateSet D.ps J b).card ≤ good.card +
    ∑ p ∈ P, (hitSet n p D.ps J b).card at cover
  have hb2 : b ≤ 2 := by rcases hb with h | h <;> omega
  have raw : (∑ p ∈ P, (hitSet n p D.ps J b).card) ≤
      ∑ p ∈ P, (2*J/(p^2)+1) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hh,hno⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨h2,hpr⟩ := (Finset.mem_filter.mp hh).2
    exact hit_card_raw D.ps hpr h2 (fun h => hno ((hreg p h2 hpr).mpr h)) hb2
  have hh := cover.trans (Nat.add_le_add hone raw)
  have hcast : ((candidateSet D.ps J b).card : ℚ) ≤
      1 + ((∑ p ∈ P, (2*J/(p^2)+1) : ℕ) : ℚ) := by exact_mod_cast hh
  change (J:ℚ) * largeRho S ≤
    ((∑ p ∈ P, (2*J/(p^2)+1) : ℕ) : ℚ) + (1 + initialError S.card)
  have initial := initial_candidates D b J hS hb
  linarith only [initial, hcast]

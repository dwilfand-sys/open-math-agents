import OMAStatements.S_oeis_a132304
import Mathlib

/-!
# The fourth-power trinomial supercongruence

Formal proof by Codex for @dwilfand-sys. Peter Bala proposed the congruence
in OEIS A132304 on 29 August 2025. The same coefficient comparison is
used for the fifth powers in the companion submission #13072. @sntntHb formalized its statement.
For the related cube case, @rbajaj5 previously gave a Frobenius-logarithm
proof in a183068-supercongruence/related-results/A132303TrinomialCubeTower.md.

Here we clear denominators in finite products for ordinary and multiset
binomial coefficients. Pairing i with p*j-i transfers the lower row modulo
p^(2*k). The identity (1+x+x²)=(1-x³)/(1-x) then gives the trinomial
coefficient transfer. Raising to the fourth power removes the off-grid terms.

Sources: https://oeis.org/A132304 and
https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A132303TrinomialCubeTower.md
-/

namespace A132304.BinomialPairs

open scoped BigOperators

theorem choose_row_identity (s j : ℕ) :
    (j + 1) * (s + 1).choose (j + 1) = (s + 1) * s.choose j := by
  simpa only [mul_comm] using (Nat.add_one_mul_choose_eq s j).symm

theorem multichoose_row_identity (s j : ℕ) :
    (j + 1) * s.multichoose (j + 1) = s * (s + j).choose j := by
  rw [Nat.multichoose_eq, show s + (j + 1) - 1 = s + j by omega]
  have h := Nat.choose_succ_right_eq (s + j) j
  rw [show s + j - j = s by omega] at h
  simpa only [mul_comm] using h

theorem choose_off_grid (p k n j : ℕ) (hp : p.Prime)
    (hn : p ^ k ∣ n) (hj : ¬p ∣ j) : p ^ k ∣ n.choose j := by
  cases j with
  | zero => exact False.elim (hj (dvd_zero p))
  | succ j =>
    cases n with
    | zero => simp
    | succ s =>
      have hc : Nat.Coprime (p ^ k) (j + 1) :=
        (hp.coprime_pow_of_not_dvd hj).symm
      apply hc.dvd_of_dvd_mul_left
      rw [choose_row_identity]
      exact dvd_mul_of_dvd_left hn _

theorem multichoose_off_grid (p k n j : ℕ) (hp : p.Prime)
    (hn : p ^ k ∣ n) (hj : ¬p ∣ j) : p ^ k ∣ n.multichoose j := by
  cases j with
  | zero => exact False.elim (hj (dvd_zero p))
  | succ j =>
    have hc : Nat.Coprime (p ^ k) (j + 1) :=
      (hp.coprime_pow_of_not_dvd hj).symm
    apply hc.dvd_of_dvd_mul_left
    rw [multichoose_row_identity]
    exact dvd_mul_of_dvd_left hn _

theorem replace_scaled_factors {α R : Type*} [CommRing R]
    (indices : Finset α) (f g : α → R) (C : R)
    (h : ∀ i ∈ indices, C * f i = C * g i) :
    C * (∏ i ∈ indices, f i) = C * (∏ i ∈ indices, g i) := by
  classical
  revert h
  induction indices using Finset.induction_on with
  | empty =>
    intro h
    simp
  | insert i s hi ih =>
    intro h
    have head := h i (Finset.mem_insert_self i s)
    have tail := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    calc
      C * (f i * ∏ j ∈ s, f j) = (C * f i) * ∏ j ∈ s, f j := by ring
      _ = (C * g i) * ∏ j ∈ s, f j := by rw [head]
      _ = g i * (C * ∏ j ∈ s, f j) := by ring
      _ = g i * (C * ∏ j ∈ s, g j) := by rw [tail]
      _ = C * (g i * ∏ j ∈ s, g j) := by ring

theorem cancel_cleared_product {R : Type*} [CommRing R]
    (upper lower numerator denominator inverse : R)
    (hclear : upper * denominator = lower * numerator)
    (hpairs : lower * numerator = lower * denominator)
    (hunit : denominator * inverse = 1) : upper = lower := by
  calc
    upper = upper * (denominator * inverse) := by rw [hunit, mul_one]
    _ = (upper * denominator) * inverse := by ring
    _ = (lower * denominator) * inverse := by rw [hclear, hpairs]
    _ = lower * (denominator * inverse) := by ring
    _ = lower := by rw [hunit, mul_one]

end A132304.BinomialPairs

namespace A132304.BinomialPairs

open Finset
open scoped BigOperators

def offIndices (p j : ℕ) : Finset ℕ :=
  (range (p * j)).filter (fun i => ¬p ∣ i)

theorem mem_offIndices {p j i : ℕ} :
    i ∈ offIndices p j ↔ i < p * j ∧ ¬p ∣ i := by
  simp only [offIndices, mem_filter, mem_range]

private theorem split_indices (p j : ℕ) (hp : 0 < p) (f : ℕ → ℤ) :
    (∏ i ∈ range (p * j), f i) =
      (∏ t ∈ range j, f (p * t)) * (∏ i ∈ offIndices p j, f i) := by
  classical
  have himage : (range (p * j)).filter (fun i => p ∣ i) =
      (range j).image (fun t => p * t) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hlt, t, rfl⟩
      exact ⟨t, (Nat.mul_lt_mul_left hp).mp hlt, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hp).mpr ht, ⟨t, rfl⟩⟩
  have hinj : Function.Injective (fun t : ℕ => p * t) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left hp h
  calc
    (∏ i ∈ range (p * j), f i) =
        (∏ i ∈ (range (p*j)).filter (fun i => p ∣ i), f i) *
          (∏ i ∈ offIndices p j, f i) :=
      (prod_filter_mul_prod_filter_not (range (p*j)) (fun i => p ∣ i) f).symm
    _ = _ := by rw [himage, prod_image hinj.injOn]

private theorem split_linear (p M j : ℕ) (hp : 0 < p) (sign : ℤ) :
    (∏ i ∈ range (p*j), (((p*M : ℕ) : ℤ) + sign * (i : ℤ))) =
      (p : ℤ)^j * (∏ t ∈ range j, ((M : ℤ) + sign * (t : ℤ))) *
        (∏ i ∈ offIndices p j, (((p*M : ℕ) : ℤ) + sign * (i : ℤ))) := by
  rw [split_indices p j hp (fun i : ℕ => ((p*M : ℕ) : ℤ) + sign * (i : ℤ))]
  congr 1
  calc
    (∏ t ∈ range j, (((p*M : ℕ) : ℤ) + sign * ((p*t : ℕ) : ℤ))) =
        ∏ t ∈ range j, ((p : ℤ) * ((M : ℤ) + sign * (t : ℤ))) := by
      apply prod_congr rfl
      intro t ht
      push_cast
      ring
    _ = _ := by rw [prod_mul_distrib]; simp

private theorem integer_choose_product (n j : ℕ) :
    (∏ i ∈ range j, ((n : ℤ) - (i : ℤ))) =
      (j.factorial : ℤ) * (n.choose j : ℤ) := by
  by_cases h : j ≤ n
  · have hn := (Nat.descFactorial_eq_prod_range n j).symm.trans
        (Nat.descFactorial_eq_factorial_mul_choose n j)
    calc
      (∏ i ∈ range j, ((n : ℤ) - (i : ℤ))) =
          ∏ i ∈ range j, ((n-i : ℕ) : ℤ) := by
        apply prod_congr rfl
        intro i hi
        exact (Nat.cast_sub (le_trans (Nat.le_of_lt (mem_range.mp hi)) h)).symm
      _ = _ := by exact_mod_cast hn
  · have hlt : n < j := by omega
    have hz : (∏ i ∈ range j, ((n : ℤ) - (i : ℤ))) = 0 :=
      Finset.prod_eq_zero (mem_range.mpr hlt) (sub_self _)
    simp only [hz, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]

private theorem integer_multichoose_product (n j : ℕ) :
    (∏ i ∈ range j, ((n : ℤ) + (i : ℤ))) =
      (j.factorial : ℤ) * (n.multichoose j : ℤ) := by
  have hn := (Nat.ascFactorial_eq_prod_range n j).symm.trans
      (Nat.ascFactorial_eq_factorial_mul_choose' n j)
  rw [Nat.multichoose_eq]
  exact_mod_cast hn

private theorem choose_with_factorial (p M j : ℕ) (hp : 0 < p) :
    ((p*j).factorial : ℤ) * ((p*M).choose (p*j) : ℤ) =
      (p : ℤ)^j * ((j.factorial : ℤ) * (M.choose j : ℤ)) *
        (∏ i ∈ offIndices p j, (((p*M : ℕ) : ℤ) - (i : ℤ))) := by
  rw [← integer_choose_product (p*M) (p*j), ← integer_choose_product M j]
  simpa only [neg_one_mul, ← sub_eq_add_neg] using (split_linear p M j hp (-1))

private theorem multichoose_with_factorial (p M j : ℕ) (hp : 0 < p) :
    ((p*j).factorial : ℤ) * ((p*M).multichoose (p*j) : ℤ) =
      (p : ℤ)^j * ((j.factorial : ℤ) * (M.multichoose j : ℤ)) *
        (∏ i ∈ offIndices p j, (((p*M : ℕ) : ℤ) + (i : ℤ))) := by
  rw [← integer_multichoose_product (p*M) (p*j), ← integer_multichoose_product M j]
  simpa only [one_mul] using (split_linear p M j hp 1)

theorem complement_mem_offIndices {p j i : ℕ} (hi : i ∈ offIndices p j) :
    p*j-i ∈ offIndices p j := by
  obtain ⟨hlt, hnd⟩ := mem_offIndices.mp hi
  have hpos : 0 < i := by
    by_contra! h
    apply hnd
    have : i = 0 := by omega
    simp [this]
  apply mem_offIndices.mpr
  refine ⟨by omega, ?_⟩
  intro hd
  apply hnd
  have hboth := Nat.dvd_sub (show p ∣ p*j from ⟨j, rfl⟩) hd
  rwa [show p*j-(p*j-i) = i by omega] at hboth

private theorem complement_product (p j : ℕ) :
    (∏ i ∈ offIndices p j, (((p*j : ℕ) : ℤ) - (i : ℤ))) =
      ∏ i ∈ offIndices p j, (i : ℤ) := by
  apply Finset.prod_bij' (fun i _ => p*j-i) (fun i _ => p*j-i)
  · exact fun _ hi => complement_mem_offIndices hi
  · exact fun _ hi => complement_mem_offIndices hi
  · intro i hi
    have := (mem_offIndices.mp hi).1
    omega
  · intro i hi
    have := (mem_offIndices.mp hi).1
    omega
  · intro i hi
    exact (Nat.cast_sub (Nat.le_of_lt (mem_offIndices.mp hi).1)).symm

private theorem factorial_off_product (p j : ℕ) (hp : 0 < p) :
    ((p*j).factorial : ℤ) = (p : ℤ)^j * (j.factorial : ℤ) *
      ∏ i ∈ offIndices p j, (i : ℤ) := by
  have h := choose_with_factorial p j j hp
  simpa only [Nat.choose_self, Nat.cast_one, mul_one, complement_product] using h

theorem choose_clear (p M j : ℕ) (hp : 0 < p) :
    ((p*M).choose (p*j) : ℤ) * (∏ i ∈ offIndices p j, (i : ℤ)) =
      (M.choose j : ℤ) *
        (∏ i ∈ offIndices p j, (((p*M : ℕ) : ℤ) - (i : ℤ))) := by
  have h := choose_with_factorial p M j hp
  rw [factorial_off_product p j hp] at h
  have hpos : 0 < (p : ℤ)^j * (j.factorial : ℤ) := by positivity
  apply mul_left_cancel₀ (ne_of_gt hpos)
  linear_combination h

theorem multichoose_clear (p M j : ℕ) (hp : 0 < p) :
    ((p*M).multichoose (p*j) : ℤ) * (∏ i ∈ offIndices p j, (i : ℤ)) =
      (M.multichoose j : ℤ) *
        (∏ i ∈ offIndices p j, (((p*M : ℕ) : ℤ) + (i : ℤ))) := by
  have h := multichoose_with_factorial p M j hp
  rw [factorial_off_product p j hp] at h
  have hpos : 0 < (p : ℤ)^j * (j.factorial : ℤ) := by positivity
  apply mul_left_cancel₀ (ne_of_gt hpos)
  linear_combination h

end A132304.BinomialPairs

namespace A132304.BinomialPairs

open scoped BigOperators

private theorem fold_complements {R : Type*} [CommMonoid R]
    (S : Finset ℕ) (J : ℕ) (f : ℕ → R)
    (bound : ∀ i ∈ S, i ≤ J) (closed : ∀ i ∈ S, J - i ∈ S)
    (nofix : ∀ i ∈ S, J - i ≠ i) :
    (∏ i ∈ S, f i) =
      ∏ i ∈ S.filter (fun i => i < J - i), f i * f (J - i) := by
  classical
  let low := S.filter (fun i => i < J - i)
  let high := S.filter (fun i => ¬i < J - i)
  have match_halves : (∏ i ∈ low, f (J - i)) = ∏ i ∈ high, f i := by
    apply Finset.prod_bij' (fun a _ => J - a) (fun a _ => J - a)
    · intro a ha
      obtain ⟨haS, haL⟩ := Finset.mem_filter.mp ha
      have hab := bound a haS
      exact Finset.mem_filter.mpr ⟨closed a haS, by omega⟩
    · intro a ha
      obtain ⟨haS, haH⟩ := Finset.mem_filter.mp ha
      have hab := bound a haS
      have han := nofix a haS
      exact Finset.mem_filter.mpr ⟨closed a haS, by omega⟩
    · intro a ha
      have h := bound a (Finset.mem_filter.mp ha).1
      omega
    · intro a ha
      have h := bound a (Finset.mem_filter.mp ha).1
      omega
    · intro a ha
      rfl
  change (∏ i ∈ S, f i) = ∏ i ∈ low, f i * f (J - i)
  rw [Finset.prod_mul_distrib, match_halves]
  exact (Finset.prod_filter_mul_prod_filter_not S (fun i => i < J - i) f).symm

private theorem off_properties (p j : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∀ i ∈ offIndices p j, i ≤ p * j) ∧
    (∀ i ∈ offIndices p j, p * j - i ∈ offIndices p j) ∧
    (∀ i ∈ offIndices p j, p * j - i ≠ i) := by
  have hJ : p ∣ p*j := dvd_mul_right p j
  have h2 : ¬p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  constructor
  · intro i hi
    exact (Finset.mem_range.mp (Finset.mem_filter.mp hi).1).le
  constructor
  · intro i hi
    obtain ⟨him, hip⟩ := Finset.mem_filter.mp hi
    have hib := Finset.mem_range.mp him
    have hiz : 0 < i := by
      by_contra! hz
      exact hip (by rw [show i = 0 by omega]; exact dvd_zero _)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    intro hc
    have h := Nat.dvd_sub hJ hc
    rw [show p*j - (p*j-i) = i by omega] at h
    exact hip h
  · intro i hi he
    obtain ⟨him, hip⟩ := Finset.mem_filter.mp hi
    have hib := Finset.mem_range.mp him
    have hti : p ∣ 2*i := by rw [show 2*i=p*j by omega]; exact hJ
    exact hip ((hp.dvd_mul.mp hti).resolve_left h2)

private theorem units_product {R : Type*} [CommMonoid R] (S : Finset ℕ)
    (f : ℕ → R) (h : ∀ i ∈ S, IsUnit (f i)) : IsUnit (∏ i ∈ S, f i) := by
  revert h
  induction S using Finset.induction_on with
  | empty => intro h; simp
  | insert i s hi ih =>
    intro h
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem transfer_cleared (p k M j upper lower L : ℕ) (rise : Bool)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hN : p ^ k ∣ p*M)
    (hrow : j*lower=M*L)
    (hclear : (upper : ZMod (p ^ (2*k))) * (∏ i ∈ offIndices p j, (i : ZMod (p ^ (2*k)))) =
      (lower : ZMod (p ^ (2*k))) * (∏ i ∈ offIndices p j,
        if rise then ((p*M : ℕ) : ZMod (p ^ (2*k))) + (i : ZMod (p ^ (2*k))) else
        ((p*M : ℕ) : ZMod (p ^ (2*k))) - (i : ZMod (p ^ (2*k))))) :
    upper ≡ lower [MOD p ^ (2*k)] := by
  classical
  let R := ZMod (p ^ (2*k))
  let S := offIndices p j
  let J := p*j
  let N := p*M
  let F : ℕ → R := fun i => if rise then (N:R) + (i:R) else (N:R) - (i:R)
  have hbound := (off_properties p j hp hp3).1
  have hclosed := (off_properties p j hp hp3).2.1
  have hnofix := (off_properties p j hp hp3).2.2
  have hsq : (N:R)^2=0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    obtain ⟨w,hw⟩ := hN
    dsimp [N]
    rw [hw, show 2*k=k*2 by omega, pow_mul, mul_pow]
    exact dvd_mul_right _ _
  have hrowN : J * lower = N * L := by
    dsimp [J,N]
    simpa only [mul_assoc] using congrArg (p * ·) hrow
  have hrowR : (J:R)*(lower:R)=(N:R)*(L:R) := by
    calc
      (J:R)*(lower:R) = ((J*lower : ℕ) : R) := (Nat.cast_mul J lower).symm
      _ = ((N*L : ℕ) : R) := congrArg (fun a : ℕ => (a:R)) hrowN
      _ = (N:R)*(L:R) := Nat.cast_mul N L
  have paired : (lower:R) * (∏ i ∈ S, F i) =
      (lower:R) * (∏ i ∈ S, (i:R)) := by
    rw [fold_complements S J F hbound hclosed hnofix,
        fold_complements S J (fun i => (i:R)) hbound hclosed hnofix]
    apply replace_scaled_factors
    intro i hi
    have hle := hbound i (Finset.mem_filter.mp hi).1
    have hsum : (i:R) + ((J-i : ℕ):R) = (J:R) := by
      rw [← Nat.cast_add, show i + (J-i)=J by omega]
    cases rise with
    | false =>
      change (lower:R) * (((N:R)-(i:R))*((N:R)-((J-i:ℕ):R))) =
        (lower:R) * ((i:R)*((J-i:ℕ):R))
      linear_combination (-(lower:R)*(N:R))*hsum - (N:R)*hrowR +
        ((lower:R)-(L:R))*hsq
    | true =>
      change (lower:R) * (((N:R)+(i:R))*((N:R)+((J-i:ℕ):R))) =
        (lower:R) * ((i:R)*((J-i:ℕ):R))
      linear_combination ((lower:R)*(N:R))*hsum + (N:R)*hrowR +
        ((lower:R)+(L:R))*hsq
  have hd : IsUnit (∏ i ∈ S, (i:R)) := by
    apply units_product
    intro i hi
    exact (ZMod.isUnit_iff_coprime i (p^(2*k))).mpr
      (hp.coprime_pow_of_not_dvd (Finset.mem_filter.mp hi).2)
  obtain ⟨u,hu⟩ := hd
  have hinv : (∏ i ∈ S, (i:R)) * (↑(u⁻¹):R) = 1 := by rw [← hu]; simp
  apply (ZMod.natCast_eq_natCast_iff upper lower (p^(2*k))).mp
  exact cancel_cleared_product _ _ _ _ _ hclear paired hinv

theorem binomial_scaled (p k n j : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hk : 0 < k) (hn : 0 < n) :
    (n * p ^ k).choose (p*j) ≡ (n * p ^ (k-1)).choose j [MOD p ^ (2*k)] := by
  cases k with
  | zero => omega
  | succ k =>
    let M := n * p^k
    have hM : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
    have he : n * p^(k+1) = p*M := by dsimp [M]; rw [pow_succ]; ring
    have hd : p ^ (k+1) ∣ p*M := by rw [← he]; exact dvd_mul_left _ _
    change (n*p^(k+1)).choose (p*j) ≡ M.choose j [MOD p^(2*(k+1))]
    rw [he]
    cases j with
    | zero => simp [Nat.ModEq]
    | succ j =>
      let L := (M-1).choose j
      have hr : (j+1)*M.choose (j+1)=M*L := by
        obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
        simpa [L,hs] using choose_row_identity s j
      apply transfer_cleared p (k+1) M (j+1) _ _ L false hp hp3 hd hr
      have hc := congrArg (Int.castRingHom (ZMod (p^(2*(k+1)))))
        (choose_clear p M (j+1) hp.pos)
      simpa using hc

theorem multichoose_scaled (p k n j : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hk : 0 < k) (hn : 0 < n) :
    (n * p ^ k).multichoose (p*j) ≡ (n * p ^ (k-1)).multichoose j
      [MOD p ^ (2*k)] := by
  cases k with
  | zero => omega
  | succ k =>
    let M := n * p^k
    have he : n * p^(k+1) = p*M := by dsimp [M]; rw [pow_succ]; ring
    have hd : p ^ (k+1) ∣ p*M := by rw [← he]; exact dvd_mul_left _ _
    change (n*p^(k+1)).multichoose (p*j) ≡ M.multichoose j [MOD p^(2*(k+1))]
    rw [he]
    cases j with
    | zero => simp [Nat.ModEq]
    | succ j =>
      let L := (M+j).choose j
      have hr : (j+1)*M.multichoose (j+1)=M*L := multichoose_row_identity M j
      apply transfer_cleared p (k+1) M (j+1) _ _ L true hp hp3 hd hr
      have hc := congrArg (Int.castRingHom (ZMod (p^(2*(k+1)))))
        (multichoose_clear p M (j+1) hp.pos)
      simpa using hc

end A132304.BinomialPairs

namespace A132304.RowBridge

open Finset OMA.S_oeis_a132304
open scoped PowerSeries

private noncomputable def term (R : Type*) [CommRing R] (N t i : ℕ) : R :=
  if 3 * i ≤ t then
    (-1 : R) ^ i * ((N.choose i : ℕ) : R) * ((N.multichoose (t - 3 * i) : ℕ) : R)
  else 0

private lemma cast_trinomial (R : Type*) [CommRing R] (N t : ℕ) :
    (trinomial N t : R) =
      PowerSeries.coeff t ((1 + PowerSeries.X + PowerSeries.X ^ 2 : R⟦X⟧) ^ N) := by
  let f : Polynomial ℕ := (1 + Polynomial.X + Polynomial.X ^ 2) ^ N
  have hmap : f.map (Nat.castRingHom R) =
      (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial R) ^ N := by
    simp [f]
  calc
    (trinomial N t : R) = (f.map (Nat.castRingHom R)).coeff t := by
      change (Nat.castRingHom R) (f.coeff t) = (f.map (Nat.castRingHom R)).coeff t
      rw [Polynomial.coeff_map]
    _ = ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial R) ^ N).coeff t := by rw [hmap]
    _ = _ := by
      rw [← Polynomial.coeff_coe]
      simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_one]

private lemma coeff_inv (R : Type*) [CommRing R] (N j : ℕ) (hN : 0 < N) :
    PowerSeries.coeff j (PowerSeries.invOneSubPow R N).val =
      ((N.multichoose j : ℕ) : R) := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos R N hN,
    PowerSeries.coeff_mk, Nat.multichoose_eq]
  have h : N - 1 + j = N + j - 1 := by omega
  rw [← h]
  exact congrArg (fun x : ℕ => (x : R))
    (Nat.choose_symm_of_eq_add (show N - 1 + j = (N - 1) + j by rfl))

private lemma trinomial_sum (R : Type*) [CommRing R] (N t : ℕ) (hN : 0 < N) :
    (trinomial N t : R) = ∑ i ∈ range (N + 1), term R N t i := by
  let u := (PowerSeries.invOneSubPow R N).val
  have cancel : (1 - PowerSeries.X : R⟦X⟧) ^ N * u = 1 := by
    simpa [u] using PowerSeries.one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow R 0 N
  have factor :
      (1 + PowerSeries.X + PowerSeries.X ^ 2 : R⟦X⟧) ^ N =
      (-PowerSeries.X ^ 3 + 1 : R⟦X⟧) ^ N * u := by
    have hx : (-PowerSeries.X ^ 3 + 1 : R⟦X⟧) =
        (1 + PowerSeries.X + PowerSeries.X ^ 2) * (1 - PowerSeries.X) := by ring
    rw [hx, mul_pow, mul_assoc, cancel, mul_one]
  rw [cast_trinomial, factor, add_pow, sum_mul, map_sum]
  apply sum_congr rfl
  intro i _
  simp only [one_pow, mul_one]
  have he :
      ((-(PowerSeries.X ^ 3) : R⟦X⟧) ^ i * (N.choose i : R⟦X⟧)) * u =
      PowerSeries.C ((-1 : R) ^ i * (N.choose i : R)) * (PowerSeries.X ^ (3 * i) * u) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, pow_mul]
    rw [show (-(PowerSeries.X ^ 3) : R⟦X⟧) = (-1) * PowerSeries.X ^ 3 by ring, mul_pow] <;>
      ac_rfl
  rw [he, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases h : 3 * i ≤ t
  · simp [term, h, u, coeff_inv R N _ hN]
  · simp [term, h]

private lemma sum_grid {R : Type*} [AddCommMonoid R] (p M : ℕ) (hp : 0 < p)
    (f : ℕ → R) (h : ∀ i, ¬p ∣ i → f i = 0) :
    ∑ i ∈ range (p*M + 1), f i = ∑ j ∈ range (M + 1), f (p*j) := by
  classical
  let s := (range (M + 1)).image (fun j => p*j)
  have subset : s ⊆ range (p*M + 1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    have hj' : j ≤ M := by simpa using hj
    simpa using Nat.mul_le_mul_left p hj'
  calc
    (∑ i ∈ range (p*M + 1), f i) = ∑ i ∈ s, f i := by
      symm
      apply sum_subset subset
      intro i hi hni
      apply h
      rintro ⟨j, rfl⟩
      apply hni
      apply mem_image.mpr
      refine ⟨j, ?_, rfl⟩
      have hj : p*j ≤ p*M := by simpa using hi
      simpa using (Nat.le_of_mul_le_mul_left hj hp)
    _ = _ := by
      dsimp [s]
      rw [sum_image]
      intro i _ j _ he
      exact Nat.eq_of_mul_eq_mul_left hp he

private lemma off_remainder (p t i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : 3*i ≤ p*t) (hi : ¬p ∣ i) : ¬p ∣ p*t - 3*i := by
  intro hd
  have h3 : p ∣ 3*i := by
    have hx : p*t - (p*t - 3*i) = 3*i := by omega
    rw [← hx]
    exact Nat.dvd_sub (dvd_mul_right p t) hd
  rcases hp.dvd_mul.mp h3 with hthree | hdiv
  · have := Nat.le_of_dvd (by decide : 0 < 3) hthree
    omega
  · exact hi hdiv

theorem row_bounds_of_binomials (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hk : 0 < k)
    (cs : ∀ i, (n*p^k).choose (p*i) ≡ (n*p^(k-1)).choose i [MOD p^(2*k)])
    (ms : ∀ i, (n*p^k).multichoose (p*i) ≡ (n*p^(k-1)).multichoose i [MOD p^(2*k)])
    (coff : ∀ i, ¬p ∣ i → p^k ∣ (n*p^k).choose i)
    (moff : ∀ i, ¬p ∣ i → p^k ∣ (n*p^k).multichoose i) :
    (∀ j, trinomial (n*p^k) (p*j) ≡ trinomial (n*p^(k-1)) j [MOD p^(2*k)]) ∧
    (∀ j, ¬p ∣ j → p^k ∣ trinomial (n*p^k) j) := by
  let N := n*p^k
  let M := n*p^(k-1)
  have hN : 0 < N := Nat.mul_pos hn (pow_pos hp.pos _)
  have hM : 0 < M := Nat.mul_pos hn (pow_pos hp.pos _)
  have hNM : N = p*M := by
    cases k with
    | zero => omega
    | succ k => simp [N, M, pow_succ]; ring
  constructor
  · intro j
    let R := ZMod (p^(2*k))
    change trinomial N (p*j) ≡ trinomial M j [MOD p^(2*k)]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [trinomial_sum R N (p*j) hN, trinomial_sum R M j hM]
    have hoff : ∀ i, ¬p ∣ i → term R N (p*j) i = 0 := by
      intro i hi
      by_cases h : 3*i ≤ p*j
      · have hboth : p^(2*k) ∣ N.choose i * N.multichoose (p*j-3*i) := by
          rw [show 2*k = k+k by omega, pow_add]
          exact Nat.mul_dvd_mul (coff i hi) (moff _ (off_remainder p j i hp hp5 h hi))
        have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hboth
        rw [term, if_pos h, mul_assoc, ← Nat.cast_mul]
        simpa [R] using congrArg (fun x : ZMod (p^(2*k)) => (-1)^i*x) hz
      · simp [term, h]
    calc
      (∑ i ∈ range (N+1), term R N (p*j) i) =
          ∑ i ∈ range (M+1), term R N (p*j) (p*i) := by
        have hsum := sum_grid p M hp.pos _ hoff
        rw [← hNM] at hsum
        exact hsum
      _ = _ := by
        apply sum_congr rfl
        intro i _
        have hind : 3*(p*i) = p*(3*i) := by ring
        have hle : 3*(p*i) ≤ p*j ↔ 3*i ≤ j := by
          rw [hind]
          exact ⟨fun h => Nat.le_of_mul_le_mul_left h hp.pos, Nat.mul_le_mul_left p⟩
        have hrem : p*j - 3*(p*i) = p*(j-3*i) := by rw [hind, Nat.mul_sub]
        have hs : (-1 : R)^(p*i) = (-1 : R)^i := by
          rw [pow_mul, (hp.odd_of_ne_two (by omega)).neg_one_pow]
        have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (cs i)
        have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (ms (j-3*i))
        by_cases hi : 3*i ≤ j
        · simp only [term, if_pos hi, if_pos (hle.mpr hi), hrem, hs]
          rw [show ((N.choose (p*i) : ℕ) : R) = (M.choose i : ℕ) from hc,
            show ((N.multichoose (p*(j-3*i)) : ℕ) : R) = (M.multichoose (j-3*i) : ℕ) from hm]
        · simp [term, hi, hle]
  · intro j hj
    let R := ZMod (p^k)
    change p^k ∣ trinomial N j
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [trinomial_sum R N j hN]
    apply sum_eq_zero
    intro i _
    by_cases h : 3*i ≤ j
    · by_cases hi : p ∣ i
      · have hr : ¬p ∣ j-3*i := by
          intro hd
          apply hj
          rw [← Nat.sub_add_cancel h]
          exact dvd_add hd (dvd_mul_of_dvd_right hi 3)
        have hz := (ZMod.natCast_eq_zero_iff _ _).mpr (moff _ hr)
        simp [term, h, N, R, hz]
      · have hz := (ZMod.natCast_eq_zero_iff _ _).mpr (coff _ hi)
        simp [term, h, N, R, hz]
    · simp [term, h]

end A132304.RowBridge

open Finset
open OMA.S_oeis_a132304

namespace A132304

private lemma multiples_in_range (p B : ℕ) (hp : 0 < p) :
    (range (p * B + 1)).filter (fun j => p ∣ j) =
      (range (B + 1)).image (fun j => p * j) := by
  ext i
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hi, j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    by_contra! h
    have hj : B < j := by omega
    have := Nat.mul_lt_mul_of_pos_left hj hp
    omega
  · rintro ⟨j, hj, rfl⟩
    exact ⟨by have := Nat.mul_le_mul_left p (show j ≤ B by omega); omega, j, rfl⟩

theorem moment_of_coefficient_bounds (p B k h : ℕ) (hp : 0 < p) (hh : 2 ≤ h)
    (upper lower : ℕ → ℕ)
    (scaled : ∀ j, upper (p*j) ≡ lower j [MOD p^(2*k)])
    (off : ∀ j, ¬ p ∣ j → p^k ∣ upper j) :
    (∑ i ∈ range (p*B+1), (upper i)^h) ≡
      ∑ j ∈ range (B+1), (lower j)^h [MOD p^(2*k)] := by
  let s := range (p*B+1)
  have clear :
      (∑ i ∈ s.filter (fun i => ¬ p ∣ i), (upper i)^h) ≡ 0 [MOD p^(2*k)] := by
    apply Nat.ModEq.sum_zero
    intro i hi
    obtain ⟨d, hd⟩ := off i (mem_filter.mp hi).2
    apply Nat.modEq_zero_iff_dvd.mpr
    refine ⟨d^2 * (upper i)^(h-2), ?_⟩
    have hp2 : p^(2*k) = (p^k)^2 := by
      rw [show 2*k = k*2 by omega, pow_mul]
    calc
      (upper i)^h = (upper i)^2 * (upper i)^(h-2) := by
        rw [← pow_add, show 2+(h-2) = h by omega]
      _ = p^(2*k) * (d^2 * (upper i)^(h-2)) := by
        rw [hp2, hd]
        ring
  have kept :
      (∑ i ∈ s.filter (fun i => p ∣ i), (upper i)^h) ≡
        ∑ j ∈ range (B+1), (lower j)^h [MOD p^(2*k)] := by
    dsimp only [s]
    rw [multiples_in_range p B hp, sum_image]
    · exact Nat.ModEq.sum (fun j _ => (scaled j).pow h)
    · intro j _ j' _ he
      exact Nat.eq_of_mul_eq_mul_left hp he
  rw [← sum_filter_add_sum_filter_not s (fun i => p ∣ i) (fun i => (upper i)^h)]
  simpa only [add_zero] using kept.add clear

theorem fourth_of_coefficient_bounds (p n k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (scaled : ∀ j, trinomial (n*p^k) (p*j) ≡
      trinomial (n*p^(k-1)) j [MOD p^(2*k)])
    (off : ∀ j, ¬p ∣ j → p^k ∣ trinomial (n*p^k) j) :
    a (n*p^k) ≡ a (n*p^(k-1)) [MOD p^(2*k)] := by
  unfold a
  have endpoint : 2*(n*p^k) = p*(2*(n*p^(k-1))) := by
    cases k with
    | zero => omega
    | succ k => simp [pow_succ] <;> ring
  rw [endpoint]
  exact moment_of_coefficient_bounds p _ k 4 hp.pos (by decide) _ _ scaled off

end A132304

theorem OMA.solution : type_of% @OMA.S_oeis_a132304.main := by
  intro p n k hp hp5 hn hk
  have hd : p ^ k ∣ n * p ^ k := dvd_mul_left _ _
  have rows := A132304.RowBridge.row_bounds_of_binomials p n k hp hp5 hn hk
    (fun j => A132304.BinomialPairs.binomial_scaled p k n j hp (by omega) hk hn)
    (fun j => A132304.BinomialPairs.multichoose_scaled p k n j hp (by omega) hk hn)
    (fun j hj => A132304.BinomialPairs.choose_off_grid p k _ j hp hd hj)
    (fun j hj => A132304.BinomialPairs.multichoose_off_grid p k _ j hp hd hj)
  exact A132304.fourth_of_coefficient_bounds p n k hp hk rows.1 rows.2

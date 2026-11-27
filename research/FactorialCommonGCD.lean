import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-! Arithmetic behind the exact common divisor of the symmetric factorial
ratios. The lower estimates and the equality calculation are independent.
Natural subtraction is avoided in valuations by taking the difference in ℤ.
The manuscript in FactorialCommonGCD.md assembles the general argument. -/

namespace FactorialCommonGCD

def valuation (p k n s : ℕ) : ℤ :=
  (((k+1)*n).factorial.factorization p : ℤ) +
  (((k+1)*s).factorial.factorization p : ℤ) -
  (n.factorial.factorization p : ℤ) - (s.factorial.factorization p : ℤ) -
  (k : ℤ) * ((n+s).factorial.factorization p : ℤ)

/-- Removing a common factor of the valuation prime preserves the valuation.
This also applies on either coordinate axis. -/
theorem valuation_scale (p k n s : ℕ) (hp : p.Prime) :
    valuation p k (p*n) (p*s) = valuation p k n s := by
  unfold valuation
  rw [show (k+1)*(p*n) = p*((k+1)*n) by ring,
    show (k+1)*(p*s) = p*((k+1)*s) by ring, ← Nat.mul_add]
  simp only [Nat.factorization_factorial_mul hp, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

private theorem split_mul_div (m N d : ℕ) (hd : 0 < d) :
    m*N/d = m*(N/d) + m*(N%d)/d := by
  have h : m*N = m*(N%d) + d*(m*(N/d)) := by
    calc
      m*N = m*(N%d+d*(N/d)) := congrArg (m * ·) (Nat.mod_add_div N d).symm
      _ = _ := by ring
  rw [h, Nat.add_mul_div_left _ _ hd, Nat.add_comm]

def layer (k n s d : ℕ) : ℤ :=
  (((k+1)*n/d : ℕ) : ℤ) + (((k+1)*s/d : ℕ) : ℤ) -
    ((n/d : ℕ) : ℤ) - ((s/d : ℕ) : ℤ) - (k : ℤ)*(((n+s)/d : ℕ) : ℤ)

private theorem arity_floor (k n s d : ℕ) (hd : 0 < d) :
    k*((n+s)/d) + n/d + s/d ≤ ((k+1)*n)/d + ((k+1)*s)/d := by
  have scale (x : ℕ) : k*(x/d) + x/d ≤ ((k+1)*x)/d := by
    rw [split_mul_div _ _ _ hd, Nat.add_mul, Nat.one_mul]
    omega
  have left := scale n
  have right := scale s
  have separate : n/d + s/d ≤ (n+s)/d := Nat.div_add_div_le_add_div
  by_cases h : (n+s)/d = n/d+s/d
  · rw [h, Nat.mul_add]
    omega
  · have carry : ((k+1)*(n+s))/d ≤ ((k+1)*n)/d + ((k+1)*s)/d + 1 := by
      rw [Nat.mul_add, Nat.add_div hd]
      split <;> omega
    rw [split_mul_div _ _ _ hd, Nat.add_mul, Nat.one_mul] at carry
    omega

private theorem layer_nonneg (k n s d : ℕ) (hd : 0 < d) : 0 ≤ layer k n s d := by
  have hn := arity_floor k n s d hd
  have hi : (k : ℤ)*(((n+s)/d : ℕ) : ℤ) + ((n/d : ℕ) : ℤ) + ((s/d : ℕ) : ℤ) ≤
      (((k+1)*n/d : ℕ) : ℤ) + (((k+1)*s/d : ℕ) : ℤ) := by exact_mod_cast hn
  unfold layer
  omega

private theorem valuation_eq_sum (p k n s T : ℕ) (hp : p.Prime)
    (hT : (k+1)*(n+s) < T) :
    valuation p k n s = ∑ j ∈ Finset.Ico 1 T, layer k n s (p^j) := by
  have expand (x : ℕ) (hx : x < T) :
      x.factorial.factorization p = ∑ j ∈ Finset.Ico 1 T, x/p^j :=
    Nat.factorization_factorial hp ((Nat.log_le_self p x).trans_lt hx)
  have hsum : n+s ≤ (k+1)*(n+s) := by rw [Nat.add_mul, Nat.one_mul]; omega
  have hn := Nat.mul_le_mul_left (k+1) (Nat.le_add_right n s)
  have hs := Nat.mul_le_mul_left (k+1) (Nat.le_add_left s n)
  unfold valuation
  rw [expand ((k+1)*n) (by omega), expand ((k+1)*s) (by omega),
    expand n (by omega), expand s (by omega), expand (n+s) (by omega)]
  simp only [layer, Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]

/-- One unit bounds the loss from splitting a floor across the two inputs. -/
theorem lower_layer (k n s d : ℕ) (hd : 0 < d) :
    k*((n+s)/d) + n/d + s/d + ((k+1)*((n+s)%d))/d ≤
      ((k+1)*n)/d + ((k+1)*s)/d + 1 := by
  have carry : ((k+1)*(n+s))/d ≤ ((k+1)*n)/d + ((k+1)*s)/d + 1 := by
    rw [Nat.mul_add, Nat.add_div hd]
    split <;> omega
  have separate : n/d + s/d ≤ (n+s)/d := Nat.div_add_div_le_add_div
  rw [split_mul_div _ _ _ hd, Nat.add_mul, Nat.one_mul] at carry
  omega

/-- At levels dividing the arity, splitting the numerator has no loss. -/
theorem lower_layer_of_dvd (k n s d : ℕ) (hd : 0 < d) (hm : d ∣ k+1) :
    k*((n+s)/d) + n/d + s/d + ((k+1)*((n+s)%d))/d ≤
      ((k+1)*n)/d + ((k+1)*s)/d := by
  obtain ⟨w,hw⟩ := hm
  have exactSplit : ((k+1)*(n+s))/d = ((k+1)*n)/d + ((k+1)*s)/d := by
    rw [hw]
    simp only [Nat.mul_assoc, Nat.mul_div_cancel_left _ hd]
    exact Nat.mul_add _ _ _
  have separate : n/d + s/d ≤ (n+s)/d := Nat.div_add_div_le_add_div
  rw [split_mul_div _ _ _ hd, Nat.add_mul, Nat.one_mul] at exactSplit
  omega

/-- A nonzero residue after removing a factor of the total degree supplies
the floor of arity divided by the remaining scale. -/
theorem residue_quota (m B u q : ℕ) (hB : 0 < B) (hu : u % q ≠ 0) :
    m/q ≤ m*((B*u)%(B*q))/(B*q) := by
  rw [Nat.mul_mod_mul_left]
  have h : B*m ≤ m*(B*(u%q)) := by
    calc
      B*m = m*B*1 := by ring
      _ ≤ m*B*(u%q) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  calc
    m/q = B*m/(B*q) := (Nat.mul_div_mul_left m q hB).symm
    _ ≤ _ := Nat.div_le_div_right h

/-- The global lower bound omitting the additional exponent of the arity.
This gives the entire predicted exponent at every prime not dividing it. -/
theorem factorial_lower (p k n s : ℕ) (hp : p.Prime) (hns : n+s ≠ 0) :
    ((k+1).factorial.factorization p : ℤ) ≤
      valuation p k n s + (Nat.log p (k+1) : ℤ) := by
  let b := (n+s).factorization p
  let L := Nat.log p (k+1)
  let T := (k+1)*(n+s) + b + L + 2
  have hpB : 0 < p^b := pow_pos hp.pos _
  have hB : p^b ∣ n+s := (hp.pow_dvd_iff_le_factorization hns).mpr le_rfl
  obtain ⟨u,hu⟩ := hB
  have unit : ¬ p ∣ u := by
    rintro ⟨v,hv⟩
    have next : p^(b+1) ∣ n+s := ⟨v, by rw [hu, hv, pow_succ, Nat.mul_assoc]⟩
    have bad := (hp.pow_dvd_iff_le_factorization hns).mp next
    change b+1 ≤ b at bad
    omega
  let D := fun j : ℕ => layer k n s (p^j)
  have single (t : ℕ) (ht : t ∈ Finset.Ico 1 (L+1)) :
      (((k+1)/p^t : ℕ) : ℤ) ≤ D (b+t) + 1 := by
    have tpos : 0 < t := (Finset.mem_Ico.mp ht).1
    have rem : u % p^t ≠ 0 := by
      intro hz
      have div : p^t ∣ u := Nat.dvd_of_mod_eq_zero hz
      have pw : p ∣ p^t := by
        obtain ⟨v,hv⟩ : ∃ v, t = v+1 := ⟨t-1, by omega⟩
        rw [hv, pow_succ]
        exact Nat.dvd_mul_left _ _
      exact unit (dvd_trans pw div)
    have quota := residue_quota (k+1) (p^b) u (p^t) hpB rem
    rw [← hu, ← pow_add] at quota
    let q := p^(b+t)
    have low := lower_layer k n s q (pow_pos hp.pos _)
    have combined : k*((n+s)/q) + n/q + s/q + (k+1)/p^t ≤
        ((k+1)*n)/q + ((k+1)*s)/q + 1 := by
      change (k+1)/p^t ≤ (k+1)*((n+s)%q)/q at quota
      omega
    have z : (k : ℤ)*(((n+s)/q : ℕ) : ℤ) + ((n/q : ℕ) : ℤ) + ((s/q : ℕ) : ℤ) +
        (((k+1)/p^t : ℕ) : ℤ) ≤ (((k+1)*n/q : ℕ) : ℤ) + (((k+1)*s/q : ℕ) : ℤ) + 1 :=
      by exact_mod_cast combined
    change _ ≤ layer k n s q + 1
    unfold layer
    omega
  have summed := Finset.sum_le_sum single
  have leg : (k+1).factorial.factorization p = ∑ t ∈ Finset.Ico 1 (L+1), (k+1)/p^t :=
    Nat.factorization_factorial hp (Nat.lt_succ_self L)
  have sub : Finset.Ico (1+b) ((L+1)+b) ⊆ Finset.Ico 1 T := by
    intro j hj
    have h := Finset.mem_Ico.mp hj
    apply Finset.mem_Ico.mpr
    dsimp [T]
    omega
  have outside : ∑ j ∈ Finset.Ico (1+b) ((L+1)+b), D j ≤
      ∑ j ∈ Finset.Ico 1 T, D j :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun j _ _ => layer_nonneg _ _ _ _ (pow_pos hp.pos j))
  rw [Finset.sum_add_distrib, Finset.sum_Ico_add D 1 (L+1) b] at summed
  simp only [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul,
    mul_one] at summed
  rw [valuation_eq_sum p k n s T hp (by dsimp [T]; omega), leg]
  push_cast
  change _ ≤ (∑ j ∈ Finset.Ico 1 T, D j) + (L : ℤ)
  omega

/-- Exact valuation of the two complementary factorials at the witness.
The logarithmic subtraction is expressed as addition on the right. -/
theorem witness_factorial_gap (p m L : ℕ) (hp : p.Prime)
    (hlo : p^L ≤ m) (hhi : m < p^(L+1)) :
    m.factorial.factorization p = (p^L-1).factorial.factorization p +
      (m-p^L).factorial.factorization p + L := by
  have expand (x : ℕ) (hx : x ≤ m) :
      x.factorial.factorization p = ∑ j ∈ Finset.Ico 1 (L+1), x/p^j :=
    Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' (by omega) (lt_of_le_of_lt hx hhi))
  have term (j : ℕ) (hj : j ∈ Finset.Ico 1 (L+1)) :
      m/p^j = (p^L-1)/p^j + (m-p^L)/p^j + 1 := by
    have hjL : j ≤ L := by have := Finset.mem_Ico.mp hj; omega
    let q := p^j
    let w := p^(L-j)
    have hq : 0 < q := pow_pos hp.pos _
    have hw : 0 < w := pow_pos hp.pos _
    have hP : p^L = q*w := by dsimp [q,w]; rw [← pow_add]; congr 1; omega
    change m/q = (p^L-1)/q + (m-p^L)/q + 1
    have pred : (q*w-1)/q + 1 = w := by
      obtain ⟨v,hv⟩ : ∃ v : ℕ, w = v+1 := ⟨w-1, by omega⟩
      rw [hv]
      have split : q*(v+1)-1 = (q-1)+q*v := by rw [Nat.mul_add, Nat.mul_one]; omega
      rw [split, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (by omega : q-1 < q)]
      omega
    have le : w ≤ m/q := (Nat.le_div_iff_mul_le hq).mpr (by simpa [hP, Nat.mul_comm] using hlo)
    rw [hP, Nat.sub_mul_div_of_le _ _ _ (hP ▸ hlo)]
    omega
  rw [expand m le_rfl, expand (p^L-1) (by omega), expand (m-p^L) (by omega)]
  calc
    _ = ∑ j ∈ Finset.Ico 1 (L+1), ((p^L-1)/p^j + (m-p^L)/p^j + 1) :=
      Finset.sum_congr rfl term
    _ = _ := by simp [Finset.sum_add_distrib]

end FactorialCommonGCD

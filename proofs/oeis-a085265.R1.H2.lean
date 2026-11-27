import OMAReductions.R_oeis_a085265_R1
import Mathlib

/-!
For squarefree n, the possible square divisors of n-(2j)^2 exclude at most one root in each half-period. Summing these exclusions with a prime-counting bound modulo 30 leaves a positive even square.
-/

open scoped BigOperators

namespace A085265Sieve

private def primeWeight (p : ℕ) : ℕ := if 2 < p ∧ p.Prime then 1 else 0

private def wheelWeight (n : ℕ) : ℕ :=
  if n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 then 1 else 0

private lemma count_eq_sum (n : ℕ) :
    ((Finset.range n).filter fun p => 2 < p ∧ p.Prime).card =
      ∑ p ∈ Finset.range n, primeWeight p := by
  simpa only [primeWeight, Nat.cast_id] using
    (Finset.sum_boole (R := ℕ) (fun p : ℕ => 2 < p ∧ p.Prime) (Finset.range n)).symm

private lemma prime_block (n : ℕ) (hn : 5 < n) :
    ((Finset.range (n + 30)).filter fun p => 2 < p ∧ p.Prime).card ≤
      ((Finset.range n).filter fun p => 2 < p ∧ p.Prime).card + 8 := by
  have count : ∀ r : Fin 30, (∑ i ∈ Finset.range 30, wheelWeight (r.val+i)) = 8 := by
    decide +kernel
  have hsum : (∑ i ∈ Finset.range 30, primeWeight (n+i)) ≤
      ∑ i ∈ Finset.range 30, wheelWeight (n%30+i) := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : 2 < n+i ∧ (n+i).Prime
    · have hnd {d : ℕ} (hd : d.Prime) (hlt : d < n+i) : ¬ d ∣ n+i := by
        intro hdvd
        exact (ne_of_lt hlt) ((Nat.prime_dvd_prime_iff_eq hd h.2).mp hdvd)
      have h2 := hnd Nat.prime_two (by omega)
      have h3 := hnd Nat.prime_three (by omega)
      have h5 := hnd (d := 5) (by decide) (by omega)
      have hr : (n%30+i)%2 ≠ 0 ∧ (n%30+i)%3 ≠ 0 ∧ (n%30+i)%5 ≠ 0 := by omega
      simp [primeWeight, wheelWeight, h, hr]
    · simp [primeWeight, h]
  have h8 := count ⟨n%30, Nat.mod_lt _ (by decide)⟩
  change (∑ i ∈ Finset.range 30, wheelWeight (n%30+i)) = 8 at h8
  rw [count_eq_sum, count_eq_sum, Finset.sum_range_add]
  exact Nat.add_le_add_left (hsum.trans_eq h8) _

theorem primeCountWheel (J : ℕ) (hJ : 10 ≤ J) :
    15 * ((Finset.range (2*J+2)).filter (fun p => 2 < p ∧ Nat.Prime p)).card ≤ 8*J+34 := by
  induction J using Nat.strong_induction_on with
  | h J ih =>
    by_cases hs : J < 25
    · have base : ∀ j : Fin 25, 10 ≤ j.val →
          15 * ((Finset.range (2*j.val+2)).filter
            (fun p => 2 < p ∧ Nat.Prime p)).card ≤ 8*j.val+34 := by decide +kernel
      exact base ⟨J,hs⟩ hJ
    · let k := J - 15
      have hk : 10 ≤ k := by dsimp [k]; omega
      have hkJ : k < J := by dsimp [k]; omega
      have hJk : J = k + 15 := by dsimp [k]; omega
      have head := ih k hkJ hk
      have tail := prime_block (2*k+2) (by omega)
      rw [show 2*J+2 = (2*k+2)+30 by omega]
      omega

end A085265Sieve

namespace A085265Sieve

private def weight (p : ℕ) : ℚ :=
  if 2 < p ∧ Nat.Prime p then 1 / (p : ℚ)^2 else 0

private def weightSum (j : ℕ) : ℚ := ∑ p ∈ Finset.range (2*j+2), weight p

private theorem weight_step (j : ℕ) (hj : 1 ≤ j) :
    weightSum (j+1) = weightSum j + weight (2*j+3) := by
  have hnot : ¬ Nat.Prime (2*j+2) := by
    intro hp
    have hd : 2 ∣ 2*j+2 := ⟨j+1, by omega⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  have hz : weight (2*j+2) = 0 := by simp [weight,hnot]
  unfold weightSum
  rw [show 2*(j+1)+2 = (2*j+2)+1+1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ, hz, add_zero]

/-- The reciprocals of the odd squares are bounded by differences of reciprocal
successive multiples of four. -/
private theorem weight_bound (j : ℕ) :
    weight (2*j+3) ≤ 1/(4*((j:ℚ)+1)) - 1/(4*((j:ℚ)+2)) := by
  have h₁ : 0 < (j:ℚ)+1 := by positivity
  have h₂ : 0 < (j:ℚ)+2 := by positivity
  have hid : (1:ℚ)/(4*((j:ℚ)+1)) - 1/(4*((j:ℚ)+2)) =
      1/(4*((j:ℚ)+1)*((j:ℚ)+2)) := by
    field_simp [h₁.ne',h₂.ne'] <;> ring
  rw [hid]
  unfold weight
  split
  · push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · positivity

private theorem weight_sum_bound (j : ℕ) (hj : 4 ≤ j) : weightSum j < 2/9 := by
  have step (k : ℕ) : weightSum (4+k) ≤
      1/9 + 1/25 + 1/49 + 1/20 - 1/(4*(((4+k : ℕ):ℚ)+1)) := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show 4+k.succ = (4+k)+1 by omega, weight_step _ (by omega)]
      have hw := weight_bound (4+k)
      push_cast at ih hw ⊢
      convert add_le_add ih hw using 1 <;> ring
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
  have hpos : 0 < (1:ℚ)/(4*(((4+k : ℕ):ℚ)+1)) := by positivity
  linarith [step k]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_budgets : ∀ t : Fin 103, 10 ≤ t.val →
    (∑ p ∈ (Finset.range (2*t.val+2)).filter (fun p => 2 < p ∧ Nat.Prime p),
      (2*t.val)/(p^2)+1) < t.val := by decide +kernel

theorem squareSieveBudget (J : ℕ) (hJ : 10 ≤ J) :
    (∑ p ∈ (Finset.range (2*J+2)).filter (fun p => 2 < p ∧ Nat.Prime p),
      (2*J)/(p^2)+1) < J := by
  by_cases hj : J < 103
  · exact small_budgets ⟨J,hj⟩ hJ
  let P := (Finset.range (2*J+2)).filter (fun p => 2 < p ∧ Nat.Prime p)
  have hposJ : (0:ℚ) < J := by exact_mod_cast (by omega : 0 < J)
  have hcard : (15:ℚ)*P.card ≤ 8*(J:ℚ)+34 := by
    exact_mod_cast primeCountWheel J hJ
  have hsum : (∑ p ∈ P, (1:ℚ)/(p:ℚ)^2) = weightSum J := by
    simp [P,weightSum,weight,Finset.sum_filter]
  have hpoint (p : ℕ) (hp : p ∈ P) : ((2*J/(p^2):ℕ):ℚ) ≤
      (2*(J:ℚ))*(1/(p:ℚ)^2) := by
    have hp0 : 0 < p := lt_trans (by decide : 0<2) (Finset.mem_filter.mp hp).2.1
    rw [mul_one_div]
    apply (le_div_iff₀ (show 0<(p:ℚ)^2 by positivity)).mpr
    exact_mod_cast Nat.div_mul_le_self (2*J) (p^2)
  have htotal : ((∑ p ∈ P, (2*J)/(p^2)+1 : ℕ):ℚ) ≤
      (2*(J:ℚ))*weightSum J + P.card := by
    push_cast
    calc
      _ ≤ ∑ p ∈ P, ((2*(J:ℚ))*(1/(p:ℚ)^2)+1) :=
          Finset.sum_le_sum (fun p hp => add_le_add_right (hpoint p hp) 1)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]; simp
  have ht : (2*(J:ℚ))*weightSum J < (2*(J:ℚ))*(2/9) :=
    mul_lt_mul_of_pos_left (weight_sum_bound J (by omega)) (by positivity)
  have hJr : (103:ℚ) ≤ J := by exact_mod_cast (by omega : 103 ≤ J)
  have hfinal : ((∑ p ∈ P, (2*J)/(p^2)+1 : ℕ):ℚ) < J := by linarith
  exact_mod_cast hfinal

end A085265Sieve

namespace A085265Sieve

/-- Two square roots with the same prime-square divisor agree up to sign. -/
private theorem root_alternatives {n p a b : ℕ} (hn : Squarefree n)
    (hp : p.Prime) (hp2 : 2 < p) (hab : a ≤ b)
    (ha : (2*a)^2 ≤ n) (hb : (2*b)^2 ≤ n)
    (hpa : p^2 ∣ n - (2*a)^2) (hpb : p^2 ∣ n - (2*b)^2) :
    p^2 ∣ b-a ∨ p^2 ∣ a+b := by
  have hroot : (2*a)^2 ≡ (2*b)^2 [MOD p^2] :=
    (Nat.modEq_of_dvd' ha hpa).trans (Nat.modEq_of_dvd' hb hpb).symm
  let d := b-a
  have heqb : b = a+d := by dsimp [d]; omega
  have heq : (2*b)^2 = (2*a)^2 + 4*(d*(a+b)) := by rw [heqb]; ring
  have hdiff := hroot.dvd'
  rw [heq, Nat.add_sub_cancel_left] at hdiff
  have hc2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr fun hd =>
    (not_le.mpr hp2) (Nat.le_of_dvd (by decide) hd)
  have hc4 : (p^2).Coprime 4 := by
    simpa using (hc2.pow_left 2).pow_right 2
  have hprod : p^2 ∣ d*(a+b) := hc4.dvd_of_dvd_mul_left hdiff
  by_cases hd : p ∣ d
  · left
    have hcop : p.Coprime (a+b) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hs
      have hu : p ∣ 2*a := by
        have h := Nat.dvd_sub hs hd
        have he : a+b-d = 2*a := by omega
        rwa [he] at h
      obtain ⟨u, hu⟩ := hu
      have hsq : p^2 ∣ (2*a)^2 := ⟨u^2, by rw [hu]; ring⟩
      have hpn : p^2 ∣ n := by
        simpa only [Nat.sub_add_cancel ha] using dvd_add hpa hsq
      exact (Nat.squarefree_iff_prime_squarefree.mp hn p hp) (by simpa [pow_two] using hpn)
    exact (hcop.pow_left 2).dvd_of_dvd_mul_right hprod
  · right
    exact ((hp.coprime_iff_not_dvd.mpr hd).pow_left 2).dvd_of_dvd_mul_left hprod

/-- An interval between two successive half-multiples of the modulus contains at
most one of an opposite pair of residue classes. -/
private theorem same_half_period {a b m : ℕ} (hm : 0 < m) (hab : a ≤ b)
    (hq : 2*a / m = 2*b / m) (hroot : m ∣ b-a ∨ m ∣ a+b) : a = b := by
  have ha := Nat.div_add_mod' (2*a) m
  have hb := Nat.div_add_mod' (2*b) m
  rw [← hq] at hb
  have hra := Nat.mod_lt (2*a) hm
  have hrb := Nat.mod_lt (2*b) hm
  rcases hroot with hdiff | hsum
  · by_contra hne
    have h := Nat.le_of_dvd (show 0 < b-a by omega) hdiff
    omega
  · have hbase : m ∣ 2*a/m*m := Nat.dvd_mul_left m _
    have hdelta := Nat.dvd_sub hsum hbase
    by_contra hne
    have hpos : 0 < (a+b) - (2*a/m*m) := by omega
    have h := Nat.le_of_dvd hpos hdelta
    omega

private theorem bad_root_card {n J p : ℕ} (hn : Squarefree n) (hp : p.Prime)
    (hp2 : 2 < p) (hJ : ∀ j ≤ J, (2*j)^2 ≤ n) :
    ((Finset.Icc 1 J).filter (fun j => p^2 ∣ n-(2*j)^2)).card ≤ 2*J/(p^2)+1 := by
  classical
  let bad := (Finset.Icc 1 J).filter (fun j => p^2 ∣ n-(2*j)^2)
  let f (j : ℕ) := 2*j/(p^2)
  let bins := Finset.range (2*J/(p^2)+1)
  have hmono : ∀ {a b : ℕ}, a ∈ bad → b ∈ bad → a ≤ b → f a = f b → a = b := by
    intro a b ha hb hab heq
    obtain ⟨haI, hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbI, hpb⟩ := Finset.mem_filter.mp hb
    apply same_half_period (m := p^2) (pow_pos hp.pos 2) hab heq
    exact root_alternatives hn hp hp2 hab (hJ a (Finset.mem_Icc.mp haI).2)
      (hJ b (Finset.mem_Icc.mp hbI).2) hpa hpb
  have hcount : bad.card ≤ bins.card := by
    apply Finset.card_le_card_of_injOn f
    · intro j hj
      have hj' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hj')))
    · intro a ha b hb heq
      rcases le_total a b with hab | hba
      · exact hmono ha hb hab heq
      · exact (hmono hb ha hba heq.symm).symm
  simpa only [bad, bins, Finset.card_range] using hcount

/-- For a squarefree input above 400 one can always use a positive even square. -/
theorem squarefree_large (n : ℕ) (hn : Squarefree n) (h : 400 < n) :
    ∃ j : ℕ, 0 < j ∧ (2*j)^2 < n ∧ Squarefree (n-(2*j)^2) := by
  classical
  let J := (n-1).sqrt/2
  let ps := (Finset.range (2*J+2)).filter (fun p => 2 < p ∧ Nat.Prime p)
  let bad (p : ℕ) := (Finset.Icc 1 J).filter (fun j => p^2 ∣ n-(2*j)^2)
  have hJ : 10 ≤ J := by
    have h20 : 20 ≤ (n-1).sqrt := Nat.le_sqrt'.mpr (by norm_num; omega)
    dsimp [J]
    omega
  have hfit (j : ℕ) (hj : j ≤ J) : (2*j)^2 < n := by
    have hle : 2*j ≤ (n-1).sqrt := by dsimp [J] at hj; omega
    have hsq := Nat.le_sqrt'.mp hle
    omega
  by_contra hnone
  have hcover : Finset.Icc 1 J ⊆ ps.biUnion bad := by
    intro j hj
    obtain ⟨hjpos,hjle⟩ := Finset.mem_Icc.mp hj
    have hlt := hfit j hjle
    have hbad : ¬ Squarefree (n-(2*j)^2) := fun hs => hnone ⟨j, hjpos, hlt, hs⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push_neg at hbad
    obtain ⟨p,hp,hpdiv⟩ := hbad
    have hpp : p^2 ∣ n-(2*j)^2 := by simpa only [pow_two] using hpdiv
    have h2 : p ≠ 2 := by
      rintro rfl
      have hs : 2*2 ∣ (2*j)^2 := ⟨j^2, by ring⟩
      apply Nat.squarefree_iff_prime_squarefree.mp hn 2 Nat.prime_two
      simpa only [Nat.sub_add_cancel hlt.le] using dvd_add hpdiv hs
    have hple := Nat.le_of_dvd (show 0 < n-(2*j)^2 by omega) hpp
    have hpbound : p ≤ (n-1).sqrt := Nat.le_sqrt'.mpr (by
      have : 0 < (2*j)^2 := pow_pos (Nat.mul_pos (by decide) hjpos) 2
      omega)
    have hmem : p ∈ ps := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_, hp⟩
      · dsimp [J]
        omega
      · have := hp.two_le
        omega
    exact Finset.mem_biUnion.mpr ⟨p, hmem, Finset.mem_filter.mpr ⟨hj, hpp⟩⟩
  have hsum : J ≤ ∑ p ∈ ps, 2*J/(p^2)+1 := by
    calc
      J = (Finset.Icc 1 J).card := by simp
      _ ≤ (ps.biUnion bad).card := Finset.card_le_card hcover
      _ ≤ ∑ p ∈ ps, (bad p).card := Finset.card_biUnion_le
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp2,hprime⟩ := (Finset.mem_filter.mp hp).2
        exact bad_root_card hn hprime hp2 (fun j hj => (hfit j hj).le)
  exact (not_le.mpr (squareSieveBudget J hJ)) hsum

end A085265Sieve

theorem OMA.solution : OMA.R_oeis_a085265_R1.H2 := by
  intro n h hn
  exact A085265Sieve.squarefree_large n hn h

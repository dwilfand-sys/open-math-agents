import OMAReductions.R_oeis_a400795_R1
import Mathlib

/-!
Source: https://oeis.org/A400795
Credit: @dwilfand-sys

A finite covering plan lists exceptional residues modulo m. The remaining
residues each carry a prime witness which works throughout that residue
class above m. In the A400795 density manuscript the period may be enlarged
to a common multiple of every q and q−1 without changing the bad proportion.
-/

namespace OMA.R_oeis_a400795_R1_H4_R1

def H1 : Prop :=
  ∀ L : ℕ, 0 < L → ∃ m : ℕ, ∃ bad : Finset ℕ,
    0 < m ∧ L*bad.card ≤ m ∧
    ∀ r : ℕ, r < m → r ∉ bad → ∃ q : ℕ,
      q.Prime ∧ 2 < q ∧ q ∣ m ∧ q-1 ∣ m ∧
      q ∣ r+1 ∧ Nat.Coprime (q-1) (2*r+1)

def H2 : Prop :=
  let W := fun n : ℕ => (Finset.range (n+1)).filter fun q =>
    q.Prime ∧ 2 < q ∧ q ∣ n+1 ∧ Nat.Coprime (q-1) (2*n+1)
  let miss := fun N : ℕ => ((Finset.Icc 1 N).filter fun n => W n = ∅).card
  ∀ m : ℕ, ∀ bad : Finset ℕ, 0 < m →
    (∀ r : ℕ, r < m → r ∉ bad → ∃ q : ℕ,
      q.Prime ∧ 2 < q ∧ q ∣ m ∧ q-1 ∣ m ∧
      q ∣ r+1 ∧ Nat.Coprime (q-1) (2*r+1)) →
    ∀ N : ℕ, miss N ≤ m+(N/m+1)*bad.card

theorem main : H1 → H2 → OMA.R_oeis_a400795_R1.H4 := by
  intro existence count
  let W := fun n : ℕ => (Finset.range (n+1)).filter fun q =>
    q.Prime ∧ 2 < q ∧ q ∣ n+1 ∧ Nat.Coprime (q-1) (2*n+1)
  let miss := fun N : ℕ => ((Finset.Icc 1 N).filter fun n => W n = ∅).card
  change Filter.Tendsto (fun N : ℕ => (miss N : ℝ)/(N : ℝ)) Filter.atTop (nhds 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L,hL⟩ := exists_nat_gt ((2 : ℝ)/ε)
  have hLr : 0 < (L : ℝ) := lt_trans (div_pos (by norm_num) hε) hL
  have hLn : 0 < L := Nat.cast_pos.mp hLr
  obtain ⟨m,bad,hm,hsize,hcover⟩ := existence L hLn
  have hrate : (2 : ℝ)/L < ε := by
    apply (div_lt_iff₀ hLr).mpr
    simpa only [mul_comm ε] using (div_lt_iff₀ hε).mp hL
  refine ⟨max 1 (L*(m+bad.card)), ?_⟩
  intro N hN
  have hpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hN)
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hpos
  have hrem : L*((N/m)*bad.card) ≤ N := by
    calc
      L*((N/m)*bad.card) = (N/m)*(L*bad.card) := by ring
      _ ≤ (N/m)*m := Nat.mul_le_mul_left _ hsize
      _ ≤ N := Nat.div_mul_le_self _ _
  have hthreshold : L*(m+bad.card) ≤ N := (le_max_right _ _).trans hN
  have hbound : miss N ≤ m+(N/m+1)*bad.card := count m bad hm hcover N
  have hnat : L*miss N ≤ 2*N := by
    calc
      L*miss N ≤ L*(m+(N/m+1)*bad.card) := Nat.mul_le_mul_left L hbound
      _ = L*(m+bad.card) + L*((N/m)*bad.card) := by ring
      _ ≤ N+N := Nat.add_le_add hthreshold hrem
      _ = 2*N := by omega
  have hcast : ((L*miss N : ℕ) : ℝ) ≤ ((2*N : ℕ) : ℝ) := Nat.cast_le.mpr hnat
  push_cast at hcast
  have hquot : (miss N : ℝ) / N ≤ 2 / (L : ℝ) := by
    apply (div_le_div_iff₀ hNr hLr).mpr
    nlinarith only [hcast]
  have hnonneg : (0 : ℝ) ≤ (miss N : ℝ) / (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hNr.le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hquot.trans_lt hrate

end OMA.R_oeis_a400795_R1_H4_R1

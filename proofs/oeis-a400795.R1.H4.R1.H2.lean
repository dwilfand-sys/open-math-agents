import OMAReductions.R_oeis_a400795_R1_H4_R1
import Mathlib

/-!
Source: https://oeis.org/A400795
Credit: @dwilfand-sys

A witness in residue r lifts to every n≡r mod m above m. Division by m and the
remainder then inject the surviving integers into complete residue blocks.
-/

namespace A400795.Periodic

def witnesses (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter fun q =>
    q.Prime ∧ 2 < q ∧ q ∣ n+1 ∧ Nat.Coprime (q-1) (2*n+1)

private theorem lift_witness {n m q : ℕ} (hm : 0 < m) (hmn : m < n)
    (hp : q.Prime) (hq : 2 < q) (hqm : q ∣ m) (ham : q-1 ∣ m)
    (hqr : q ∣ n%m+1) (hcop : Nat.Coprime (q-1) (2*(n%m)+1)) :
    q ∈ witnesses n := by
  have hsum := Nat.div_add_mod n m
  have h1 : n+1 = m*(n/m)+(n%m+1) := by omega
  have h2 : 2*n+1 = m*(2*(n/m))+(2*(n%m)+1) := by
    calc
      2*n+1 = 2*(m*(n/m)+n%m)+1 := by rw [hsum]
      _ = _ := by ring
  have hnq : q ∣ n+1 := by
    rw [h1]
    exact dvd_add (dvd_mul_of_dvd_left hqm _) hqr
  have hcopn : Nat.Coprime (q-1) (2*n+1) := by
    change Nat.gcd (q-1) (2*n+1) = 1
    rw [h2, Nat.gcd_add_left_right_of_dvd _ (dvd_mul_of_dvd_left ham _)]
    exact hcop
  have hqn : q ≤ m := Nat.le_of_dvd hm hqm
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,hq,hnq,hcopn⟩

/-- In an initial interval, each residue occurs at most N/m+1 times. -/
theorem count_residues_le (N m : ℕ) (bad : Finset ℕ) :
    ((Finset.Icc 1 N).filter fun n => n%m ∈ bad).card ≤ (N/m+1)*bad.card := by
  let S := (Finset.Icc 1 N).filter fun n => n%m ∈ bad
  let f := fun n : ℕ => (n/m,n%m)
  have hinj : Function.Injective f := by
    intro x y h
    have hq : x/m = y/m := congrArg Prod.fst h
    have hr : x%m = y%m := congrArg Prod.snd h
    calc
      x = m*(x/m)+x%m := (Nat.div_add_mod x m).symm
      _ = m*(y/m)+y%m := by rw [hq,hr]
      _ = y := Nat.div_add_mod y m
  have hsub : S.image f ⊆ (Finset.range (N/m+1)).product bad := by
    intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hi,hr⟩ := Finset.mem_filter.mp hn
    have hle := (Finset.mem_Icc.mp hi).2
    have hq : n/m ≤ N/m := Nat.div_le_div_right hle
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),hr⟩
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.range (N/m+1)).product bad).card := Finset.card_le_card hsub
    _ = (N/m+1)*bad.card := by simp

theorem finite_bound (m : ℕ) (bad : Finset ℕ) (hm : 0 < m)
    (cover : ∀ r : ℕ, r < m → r ∉ bad → ∃ q : ℕ,
      q.Prime ∧ 2 < q ∧ q ∣ m ∧ q-1 ∣ m ∧
      q ∣ r+1 ∧ Nat.Coprime (q-1) (2*r+1)) (N : ℕ) :
    ((Finset.Icc 1 N).filter fun n => witnesses n = ∅).card ≤
      m+(N/m+1)*bad.card := by
  let small := Finset.Icc 1 m
  let residual := (Finset.Icc 1 N).filter fun n => n%m ∈ bad
  have hsub : (Finset.Icc 1 N).filter (fun n => witnesses n = ∅) ⊆ small ∪ residual := by
    intro n hn
    obtain ⟨hi,hempty⟩ := Finset.mem_filter.mp hn
    by_cases hsmall : n ≤ m
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,hsmall⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hi,?_⟩
      by_contra hbad
      obtain ⟨q,hp,hq,hqm,ham,hqr,hcop⟩ := cover (n%m) (Nat.mod_lt _ hm) hbad
      have hw := lift_witness hm (by omega : m < n) hp hq hqm ham hqr hcop
      simpa [hempty] using hw
  have hs : small.card = m := by simp [small, Nat.card_Icc]
  calc
    _ ≤ (small ∪ residual).card := Finset.card_le_card hsub
    _ ≤ small.card+residual.card := Finset.card_union_le _ _
    _ ≤ m+(N/m+1)*bad.card := by
      rw [hs]
      exact Nat.add_le_add_left (count_residues_le N m bad) m

end A400795.Periodic

theorem OMA.solution : OMA.R_oeis_a400795_R1_H4_R1.H2 := by
  intro m bad hm cover N
  exact A400795.Periodic.finite_bound m bad hm cover N

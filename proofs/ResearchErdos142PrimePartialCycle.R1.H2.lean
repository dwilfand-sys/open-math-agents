import OMAReductions.R_ResearchErdos142PrimePartialCycle_R1

/-! Exact cardinality of the prime partial-cycle construction. -/

namespace Erdos142PrimePartialCycleCard

open Finset OMA.R_ResearchErdos142PrimePartialCycle_R1

theorem partialCycle_card {A : Finset ℕ} {p t N : ℕ} (hp : 1 < p)
    (hA : A ⊆ Icc 1 N) :
    (partialCycle A p t).card =
      (p - 1) * A.card + (A.filter fun x => x % p = t).card := by
  let core := ((Ico 1 p).product A).image (fun q => q.1 + p * (q.2 - 1))
  let extra := (A.filter fun x => x % p = t).image (fun x => p * x)
  have injCore : Set.InjOn (fun q : ℕ × ℕ => q.1 + p * (q.2 - 1))
      (((Ico 1 p).product A : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    obtain ⟨hxe, hxA⟩ := mem_product.mp hx
    obtain ⟨hye, hyA⟩ := mem_product.mp hy
    have hxI := mem_Ico.mp hxe
    have hyI := mem_Ico.mp hye
    have hfirst : x.1 = y.1 := by
      have hm := congrArg (fun n : ℕ => n % p) hxy
      simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxI.2,
        Nat.mod_eq_of_lt hyI.2] using hm
    apply Prod.ext hfirst
    change x.1 + p * (x.2 - 1) = y.1 + p * (y.2 - 1) at hxy
    rw [hfirst] at hxy
    have hmul : p * (x.2 - 1) = p * (y.2 - 1) := Nat.add_left_cancel hxy
    have hsub : x.2 - 1 = y.2 - 1 := Nat.eq_of_mul_eq_mul_left (by omega) hmul
    have hxpos := (mem_Icc.mp (hA hxA)).1
    have hypos := (mem_Icc.mp (hA hyA)).1
    omega
  have injExtra : Set.InjOn (fun x : ℕ => p * x)
      ((A.filter fun x => x % p = t : Finset ℕ) : Set ℕ) := by
    intro x hx y hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  have dis : Disjoint core extra := by
    apply disjoint_left.mpr
    intro z hzcore hzextra
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hzcore
    obtain ⟨hqe, hqA⟩ := mem_product.mp hq
    obtain ⟨x, hx, heq⟩ := mem_image.mp hzextra
    have hqI := mem_Ico.mp hqe
    have hmod := congrArg (fun n : ℕ => n % p) heq
    have hcoremod : (q.1 + p * (q.2 - 1)) % p = q.1 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqI.2]
    have hextramod : (p * x) % p = 0 := by simp
    rw [hextramod, hcoremod] at hmod
    omega
  change (core ∪ extra).card = _
  rw [card_union_of_disjoint dis]
  change (((Ico 1 p).product A).image (fun q => q.1 + p * (q.2 - 1))).card +
      ((A.filter fun x => x % p = t).image (fun x => p * x)).card = _
  rw [card_image_of_injOn injCore, card_image_of_injOn injExtra]
  have hprod : ((Ico 1 p).product A).card = (p - 1) * A.card := by
    calc
      _ = (Ico 1 p).card * A.card := Finset.card_product _ _
      _ = (p - 1) * A.card := by rw [Nat.card_Ico]
  rw [hprod]
  omega

end Erdos142PrimePartialCycleCard

theorem OMA.solution : OMA.R_ResearchErdos142PrimePartialCycle_R1.H2 := by
  intro A p t N hp hA
  exact Erdos142PrimePartialCycleCard.partialCycle_card hp hA

